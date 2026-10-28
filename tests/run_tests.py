#!/usr/bin/env python3
"""Tests for the Lean XML safe-subset parser and printer.

Four parts.

1. Fixed cases: hand written documents covering each feature of
   the subset (nesting, both quote forms, empty elements in both
   spellings, attribute references and tab normalization, text
   with the five entities and numeric references in both bases,
   CDATA holding markup-like text, comments in the prolog, the
   content, and the epilog, processing instructions, mixed
   content). For each, the Lean answer must be the canonical
   print written here.

2. A differential run against Python's `xml.etree.ElementTree`,
   with a recorded seed. Random documents inside the subset are
   built as trees in Python, then spelled in XML with random
   choices that do not change the tree: quote choice, CDATA
   spellings of text, entity and character reference spellings,
   the two empty element spellings, literal whitespace in
   attribute values (which the subset normalizes to a space),
   the whitespace before each attribute (never empty), around the
   equals sign and before the end of a tag, and whitespace at the
   top level around the prolog, the root and the epilog.
   For every document:

   - the Lean tool must accept it, and its canonical print must
     equal the canonical print computed in Python from the tree;
   - ElementTree must accept it, and the tree ElementTree reads
     (for the root element; ElementTree does not keep the prolog
     and epilog) must equal the tree that was generated.

   Line ends: both sides normalize a literal carriage return and
   line feed pair, and a lone carriage return, to a line feed
   before parsing (XML 1.0 section 2.11). The generator spells a
   line feed of the tree as a line feed, a carriage return and
   line feed pair, or a lone carriage return, in text, comments,
   processing instruction data, tags and the top level. A carriage
   return in the tree's text or attribute values is spelled as a
   character reference, the only way to keep one.

3. Print then parse: every canonical print the tool gave in parts
   1 and 2 is sent back, and the answer must be the same print
   (`Spec.print_parse`, run on the compiled tool).

4. Named rejections: inputs for every rejection rule in SPEC.md,
   most of them in more than one position (at the start, after
   a prolog, after text, after other attributes, in a nested
   element). The Lean tool must reject every one. ElementTree
   agrees with most of them; where ElementTree accepts (a
   document type declaration, a colon in a name, a namespace
   declaration, the XML declaration form), that is an out of
   subset disagreement, counted apart, because the subset is
   narrower than XML by design.

Malformed request lines must be answered `error`, as in the
other slices' harnesses.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is built first with `lake build` (which does nothing
when the build is current), driven in batches of request lines,
and the results are written to tests/TEST-RESULTS.md. The run
fails closed: a tool that exits with a non-zero status, or gives
fewer or more answers than it was sent requests, is a failure, and
every failing check is counted. The exit code is non-zero if any
check fails. Python 3.11+.
"""

import argparse
import os
import pyexpat
import random
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "xml"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 2000

SEED_DEFAULT = 20261026
COUNT_DEFAULT = 3200


# ----------------------------------------------------------------
# The tree model, mirroring Xml/Value.lean.
#
# A node is one of:
#   ("text", s)
#   ("elem", name, [(attr, value), ...], [node, ...])
#   ("comment", s)
#   ("pi", target, data)
# A document is (prolog, root, epilog) with prolog and epilog
# lists of comment and pi nodes.


def escape_text(s):
    out = []
    for c in s:
        if c == "&":
            out.append("&amp;")
        elif c == "<":
            out.append("&lt;")
        elif c == ">":
            out.append("&gt;")
        elif c == "\r":
            out.append("&#13;")
        else:
            out.append(c)
    return "".join(out)


def escape_attr(s):
    out = []
    for c in s:
        if c == "&":
            out.append("&amp;")
        elif c == "<":
            out.append("&lt;")
        elif c == '"':
            out.append("&quot;")
        elif c == "\t":
            out.append("&#9;")
        elif c == "\n":
            out.append("&#10;")
        elif c == "\r":
            out.append("&#13;")
        else:
            out.append(c)
    return "".join(out)


def print_node(n):
    kind = n[0]
    if kind == "text":
        return escape_text(n[1])
    if kind == "comment":
        return "<!--" + n[1] + "-->"
    if kind == "pi":
        if n[2] == "":
            return "<?" + n[1] + "?>"
        return "<?" + n[1] + " " + n[2] + "?>"
    _, name, attrs, content = n
    parts = ["<" + name]
    for k, v in attrs:
        parts.append(" " + k + '="' + escape_attr(v) + '"')
    if not content:
        parts.append("/>")
    else:
        parts.append(">")
        for c in content:
            parts.append(print_node(c))
        parts.append("</" + name + ">")
    return "".join(parts)


def print_doc(doc):
    prolog, root, epilog = doc
    return ("".join(print_node(n) for n in prolog)
            + print_node(root)
            + "".join(print_node(n) for n in epilog))


# ----------------------------------------------------------------
# ElementTree reading, converted to the model. Only the root
# element is compared: ElementTree drops the prolog and epilog.


def et_to_model(elem):
    if elem.tag is ET.Comment:
        return ("comment", elem.text or "")
    if elem.tag is ET.ProcessingInstruction:
        text = elem.text or ""
        if " " in text:
            target, data = text.split(" ", 1)
        else:
            target, data = text, ""
        return ("pi", target, data)
    content = []
    if elem.text:
        content.append(("text", elem.text))
    for child in elem:
        content.append(et_to_model(child))
        if child.tail:
            content.append(("text", child.tail))
    return ("elem", elem.tag, list(elem.attrib.items()), content)


def et_parse(text):
    """ElementTree's reading of a text. ET.XMLParser always runs
    expat with namespace processing on; there is no subset setting.
    Documents outside the subset are therefore told apart by the
    named rejection list, not by the oracle."""
    builder = ET.TreeBuilder(insert_comments=True, insert_pis=True)
    return ET.fromstring(text, parser=ET.XMLParser(target=builder))


# ----------------------------------------------------------------
# The tool driver: one request per line, character codes.


def codes(text):
    return ",".join(str(ord(c)) for c in text)


def request(text):
    return "parse " + codes(text)


def run_tool(lines, failures, part, timeout=TIMEOUT):
    """Send the request lines to the tool and return one answer per
    line. The run fails closed: a non-zero exit status, or a number
    of answers that differs from the number of requests, is recorded
    as a failure of `part`, and missing answers read as `<missing>`,
    which no check accepts."""
    try:
        proc = subprocess.run(
            [str(EXE)], input=("\n".join(lines) + "\n").encode(),
            capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        failures.append("%s: tool did not answer within %d seconds"
                        % (part, timeout))
        return ["<missing>"] * len(lines)
    answers = proc.stdout.decode(errors="replace").splitlines()
    if proc.returncode != 0:
        failures.append("%s: tool exited with status %d"
                        % (part, proc.returncode))
    if len(answers) != len(lines):
        failures.append("%s: tool gave %d answers for %d requests"
                        % (part, len(answers), len(lines)))
        answers = (answers + ["<missing>"] * len(lines))[:len(lines)]
    return answers


def run_requests(texts, failures, part):
    lines = [request(t) for t in texts]
    answers = []
    for i in range(0, len(lines), CHUNK):
        answers.extend(run_tool(lines[i:i + CHUNK], failures, part))
    return answers


# ----------------------------------------------------------------
# Fixed cases: (input, expected canonical print).

FIXED = [
    ("<a/>", "<a/>"),
    ("<a></a>", "<a/>"),
    ("<a>x</a>", "<a>x</a>"),
    ("<a><b><c>deep</c></b></a>", "<a><b><c>deep</c></b></a>"),
    ("<a b=\"1\" c='2'>t</a>", '<a b="1" c="2">t</a>'),
    ("<a b='say \"hi\"'>x</a>", '<a b="say &quot;hi&quot;">x</a>'),
    ("<a b=\"it's\">x</a>", "<a b=\"it's\">x</a>"),
    # literal tab and newline in a value read as a space; a
    # character reference to a tab stays a tab
    ("<a b=\"x\ty\nz\"/>", '<a b="x y z"/>'),
    ("<a b=\"x&#9;y&#10;z\"/>", '<a b="x&#9;y&#10;z"/>'),
    ("<a b=\"&lt;&amp;&quot;&apos;&gt;\"/>",
     '<a b="&lt;&amp;&quot;\'>"/>'),
    ("<a>&lt;&gt;&amp;&apos;&quot;</a>", "<a>&lt;&gt;&amp;'\"</a>"),
    ("<a>&#65;&#x42;&#x63;</a>", "<a>ABc</a>"),
    ("<a>&#233;&#xE9;</a>", "<a>éé</a>"),
    ("<a>1 &gt; 0 and 2 &lt; 3</a>", "<a>1 &gt; 0 and 2 &lt; 3</a>"),
    ("<a><![CDATA[x <y> & z]]></a>", "<a>x &lt;y&gt; &amp; z</a>"),
    ("<a>t1<![CDATA[t2]]>t3</a>", "<a>t1t2t3</a>"),
    ("<a><![CDATA[]]]><![CDATA[>]]></a>", "<a>]&gt;</a>"),
    ("<!--lead--><a/><!--trail-->", "<!--lead--><a/><!--trail-->"),
    ("<a><!-- inside --></a>", "<a><!-- inside --></a>"),
    ("<!-- a - b --><a/>", "<!-- a - b --><a/>"),
    ("<?pi data?><a/>", "<?pi data?><a/>"),
    ("<?pi?><a/>", "<?pi?><a/>"),
    ("<?xml-stylesheet href=\"x\"?><a/>", "<?xml-stylesheet href=\"x\"?><a/>"),
    ("<a><?go some data here?></a>", "<a><?go some data here?></a>"),
    ("<a>x<b/>y<c>z</c>w</a>", "<a>x<b/>y<c>z</c>w</a>"),
    ("<a  b = \"1\"   c = '2' ></a>", '<a b="1" c="2"/>'),
    ("<a>x</a  >", "<a>x</a>"),
    ("<a>&#13;</a>", "<a>&#13;</a>"),
    ("<a b=\"&#13;\"/>", '<a b="&#13;"/>'),
    ("<a>text with ] and ]] but no close</a>",
     "<a>text with ] and ]] but no close</a>"),
    ("<_x.y-z_9/>", "<_x.y-z_9/>"),
    ("<a b.c-d_e=\"v\"/>", '<a b.c-d_e="v"/>'),
    ("<a>\n  spaced\n</a>", "<a>\n  spaced\n</a>"),
    ("<a><b/></a >", "<a><b/></a>"),
    ("<!--c--><?p d?><r a=\"1\">t<u/></r><!--e-->",
     "<!--c--><?p d?><r a=\"1\">t<u/></r><!--e-->"),
    # only the exact name xmlns declares a namespace; these are
    # ordinary attribute names, and an element may be named xmlns
    ("<a xmlnsx=\"v\" XMLNS=\"w\" xmln=\"u\"/>",
     '<a xmlnsx="v" XMLNS="w" xmln="u"/>'),
    ("<xmlns/>", "<xmlns/>"),
    # any whitespace separates attributes: space, tab, line feed
    ("<a\tb=\"1\"\nc='2' \t d=\"3\"\n/>", '<a b="1" c="2" d="3"/>'),
    # line ends: CR LF and a lone CR read as LF (XML 1.0 2.11),
    # everywhere; only a character reference keeps a CR
    ("<a>x\r\ny</a>", "<a>x\ny</a>"),
    ("<a>x\ry</a>", "<a>x\ny</a>"),
    ("<a>x\r\r\ny\n\rz\r</a>", "<a>x\n\ny\n\nz\n</a>"),
    ("<a>&#13;\r\n&#xD;</a>", "<a>&#13;\n&#13;</a>"),
    ("<a><![CDATA[x\r\ny\rz]]></a>", "<a>x\ny\nz</a>"),
    ("<!--a\r\nb\rc--><a/>", "<!--a\nb\nc--><a/>"),
    ("<a><?p a\r\nb\rc?></a>", "<a><?p a\nb\nc?></a>"),
    ("<a b=\"x\r\ny\rz\"/>", '<a b="x y z"/>'),
    ("\r\n<a\r\nb=\"1\"\r/>\r", '<a b="1"/>'),
    ("<a>x</a\r>", "<a>x</a>"),
]

# Named rejections: (rule, input). ElementTree's verdict is
# recorded for each; where it accepts, the case is an out of
# subset disagreement, not a failure.
REJECTIONS = [
    ("document type declaration", "<!DOCTYPE a><a/>"),
    ("document type declaration with internal subset",
     "<!DOCTYPE a [<!ENTITY e \"x\">]><a>&e;</a>"),
    ("entity declaration door (any other <! form)",
     "<a><!ENTITY e \"x\"></a>"),
    ("undefined entity", "<a>&nbsp;</a>"),
    ("undefined entity in an attribute", "<a b=\"&copy;\"/>"),
    ("mismatched tags", "<a></b>"),
    ("mismatched tags, nested", "<a><b></a></b>"),
    ("unclosed element", "<a>"),
    ("unclosed element after content", "<a><b></b>"),
    ("a second root element", "<a/><b/>"),
    ("text before the root", "x<a/>"),
    ("text after the root", "<a/>x"),
    ("duplicate attribute", "<a b=\"1\" b=\"2\"/>"),
    ("raw < in an attribute value", "<a b=\"x<y\"/>"),
    ("]]> in text", "<a>x]]>y</a>"),
    ("-- inside a comment", "<a><!-- x -- y --></a>"),
    ("comment ending in a dash", "<a><!-- x ---></a>"),
    ("surrogate character reference", "<a>&#xD800;</a>"),
    ("zero character reference", "<a>&#0;</a>"),
    ("character reference past the last character",
     "<a>&#x110000;</a>"),
    ("colon in a name", "<a:b/>"),
    ("colon in an attribute name", "<a xml:lang=\"en\"/>"),
    ("default namespace declaration", "<a xmlns=\"urn:x\"/>"),
    ("empty default namespace declaration", "<a xmlns=\"\"/>"),
    ("default namespace declaration, single quotes",
     "<a xmlns='urn:x'><b/></a>"),
    ("default namespace declaration after another attribute",
     "<a b=\"1\" xmlns=\"urn:x\"/>"),
    ("default namespace declaration on a child element",
     "<a><b xmlns=\"urn:x\"/></a>"),
    ("prefixed namespace declaration", "<a xmlns:p=\"urn:x\"/>"),
    ("name starting with a digit", "<1a/>"),
    ("attribute name starting with a digit", "<a 1b=\"x\"/>"),
    ("unquoted attribute value", "<a b=x/>"),
    ("no whitespace between attributes", "<a b=\"1\"c=\"2\"/>"),
    ("no whitespace between attributes, single quotes",
     "<a b='1'c='2'></a>"),
    ("no whitespace between attributes (W3C o-p40fail1)",
     "<doc att=\"val\"att2=\"val2\"></doc>"),
    ("no whitespace between attributes in an empty element tag",
     "<doc att=\"val\"att2=\"val2\"/>"),
    ("no whitespace between attributes on a child element",
     "<a><b c=\"1\"d=\"2\"/></a>"),
    ("missing equals", "<a b \"x\"/>"),
    ("CDATA section in the prolog", "<![CDATA[x]]><a/>"),
    ("CDATA section in the epilog", "<a/><![CDATA[x]]>"),
    ("the XML declaration form", "<?xml version=\"1.0\"?><a/>"),
    ("the XML declaration, upper case target",
     "<?XML version=\"1.0\"?><a/>"),
    ("bare ampersand in text", "<a>a & b</a>"),
    ("reference without a semicolon", "<a>&amp</a>"),
    ("empty reference", "<a>&;</a>"),
    ("hex reference with no digits", "<a>&#x;</a>"),
    ("control character reference", "<a>&#11;</a>"),
    ("raw control character in text", "<a>x\x0by</a>"),
    ("unterminated comment", "<a><!-- x</a>"),
    ("unterminated processing instruction", "<a><?p x</a>"),
    ("unterminated CDATA section", "<a><![CDATA[x</a>"),
    ("end tag with no start", "</a>"),
    # the same rules in other positions, as the general statements
    # in Spec.lean state them: after a prolog, after text, after
    # other attributes, after a whole document
    ("document type declaration after a comment",
     "<!--c--><!DOCTYPE a><a/>"),
    ("CDATA section after a processing instruction", "<?p?><![CDATA[x]]><a/>"),
    ("xml declaration target in mixed case", "<?xMl version=\"1.0\"?><a/>"),
    ("text after a prolog", "<!--c-->x<a/>"),
    ("second element after a document with an epilog", "<a/><!--c--><b/>"),
    ("digit element name after a prolog", "<?p?><9/>"),
    ("colon in a name after a prolog", "<!--c--><a:b/>"),
    ("mismatched end tag after content and attributes",
     "<a b=\"1\">x<c/></b>"),
    ("unclosed element with attributes", "<a b=\"1\">"),
    ("undefined entity after text", "<a>text &e; more</a>"),
    ("undefined entity in an attribute after text", "<a b=\"x&e;y\"/>"),
    ("surrogate reference after text", "<a>x&#xD800;</a>"),
    ("zero reference after text", "<a>x&#0;</a>"),
    ("]]> after text", "<a>text]]></a>"),
    ("-- in a comment after a well formed body",
     "<a b=\"1\"><!--ok--x--></a>"),
    ("duplicate attribute after another", "<a b=\"1\" c=\"2\" b=\"3\"/>"),
    ("raw < after text in an attribute value", "<a b=\"xy<\"/>"),
    ("unquoted value after another attribute", "<a b=\"1\" c=x/>"),
    # undefined entities where no theorem covers them (the refusal
    # statements reach the root's first text run and the root's
    # attribute values only; see SPEC.md and README)
    ("undefined entity in a nested element", "<a><b>&e;</b></a>"),
    ("undefined entity after a child element", "<a><b/>&e;</a>"),
    ("undefined entity after a comment", "<a><!--c-->&e;</a>"),
    ("undefined entity after a CDATA section",
     "<a><![CDATA[x]]>&e;</a>"),
    ("undefined entity after a predefined one", "<a>&amp;&e;</a>"),
    ("undefined entity in a nested element's attribute",
     "<a><b c=\"&e;\"/></a>"),
    ("undefined entity in an attribute after a reference",
     "<a b=\"&lt;&e;\"/>"),
    # inputs review 1 (finding 7) listed as missing
    ("hex reference with an upper case X", "<a>&#X41;</a>"),
    ("reference to a non-character", "<a>&#xFFFE;</a>"),
    ("document type declaration in content", "<a><!DOCTYPE x></a>"),
    ("xml declaration after the root", "<a/><?xml version=\"1.0\"?>"),
    ("empty document", ""),
    ("whitespace only document", "  \n "),
    ("comment only document", "<!--c-->"),
]

MALFORMED = [
    "parse x",
    "parse 60,,62",
    "parse 60, 62",
    "parse -1",
    "parse 1114112",
    "parse 55296",
    "print 60",
    "PARSE 60",
    "parse 60 62",
    "",
]

# parse with no codes is a plain empty input, not malformed:
# it must answer none (the empty text is not a document).


# ----------------------------------------------------------------
# The generator: random trees in the subset, spelled with random
# choices that do not change the tree. Each generated case is
# (spelling, model document). The model is built alongside the
# spelling, token by token, so that the two always agree: a
# literal tab spelled in an attribute value is a space in the
# model, a character reference to a tab is a tab in the model.

NAME_START = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"
NAME_CHARS = NAME_START + "0123456789.-"
TEXT_PLAIN = ("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
              "0123456789 .,;:!?()[]{}+-*/=_%$#@~^|"
              "\u00e9\u4e2d\ufffd\U0001f600")
COMMENT_WORDS = ["note", "a", "draft-1", "x", "see above", "ok",
                 "todo: fix", "caf\u00e9", "na\u00efve", "123"]


def gen_name(rng):
    n = rng.randint(1, 7)
    return rng.choice(NAME_START) + "".join(
        rng.choice(NAME_CHARS) for _ in range(n - 1))


def spell_line_end(rng, next_char):
    """One spelling of a line feed of the tree: a line feed, a
    carriage return and line feed pair, or a lone carriage return.
    A lone carriage return is chosen only when the next character
    of the spelling cannot be a literal line feed, which would
    pair with it."""
    if next_char == "\n":
        return rng.choice(["\n", "\r\n"])
    return rng.choice(["\n", "\r\n", "\r"])


def spell_text_char(rng, c, emitted, next_char=None):
    """One spelling of a text character, and it is never a raw
    less sign, a raw ampersand, or a raw greater sign right after
    two right brackets."""
    if c == "\n":
        return spell_line_end(rng, next_char)
    if c == "&":
        return "&amp;"
    if c == "<":
        return "&lt;"
    if c == ">":
        if rng.random() < 0.5:
            return "&gt;"
        return "&#62;"
    if c == "\r":
        return rng.choice(["&#13;", "&#xD;"])
    if c == "\t":
        return c
    r = rng.random()
    if r < 0.06:
        return "&#%d;" % ord(c)
    if r < 0.10:
        return "&#x%X;" % ord(c)
    return c


def gen_text_run(rng):
    """A text run: returns (spelling, model text). The spelling
    may split the run into plain pieces and CDATA sections; the
    model is one merged run."""
    n = rng.randint(1, 14)
    chars = []
    for _ in range(n):
        r = rng.random()
        if r < 0.72:
            chars.append(rng.choice(TEXT_PLAIN))
        elif r < 0.78:
            chars.append("&")
        elif r < 0.84:
            chars.append("<")
        elif r < 0.90:
            chars.append(">")
        elif r < 0.92:
            chars.append("\r")
        elif r < 0.95:
            chars.append("\n")
        elif r < 0.97:
            chars.append("'")
        else:
            chars.append('"')
    model = "".join(chars)
    # Spell it: choose up to two cut points where a CDATA section
    # starts or ends. Inside CDATA everything is literal except
    # the model holds no ]]> (it cannot: > after ]] is possible,
    # so keep CDATA pieces free of a ] ] > run by construction:
    # a CDATA piece may not end with ]] when the next model char
    # is >, and may not contain ]]> at all. The generator simply
    # avoids CDATA around ] characters.
    pieces = []
    i = 0
    emitted = ""
    while i < len(chars):
        if (rng.random() < 0.3 and chars[i] != "]"
                and (i + 1 >= len(chars) or chars[i + 1] != "]")):
            j = i
            buf = []
            while (j < len(chars) and chars[j] not in "<&"
                   and chars[j] != "\r"
                   and not (chars[j] == "]" and j + 1 < len(chars)
                            and chars[j + 1] == "]")):
                buf.append(chars[j])
                j += 1
            if buf and buf[-1] != "]":
                pieces.append("<![CDATA[" + "".join(buf) + "]]>")
                emitted += "".join(buf)
                i = j
                continue
        nxt = chars[i + 1] if i + 1 < len(chars) else None
        sp = spell_text_char(rng, chars[i], emitted, nxt)
        pieces.append(sp)
        emitted += chars[i]
        i += 1
    return "".join(pieces), model


def gen_attr_value(rng):
    """Returns (spelling inside the quotes, model value, quote).
    The quote is chosen so a literal quote of the other kind may
    appear."""
    quote = rng.choice(['"', "'"])
    toks = []
    model = []
    for _ in range(rng.randint(0, 10)):
        r = rng.random()
        if r < 0.55:
            c = rng.choice(TEXT_PLAIN)
            toks.append(c)
            model.append(c)
        elif r < 0.62:
            toks.append("\t")       # literal tab: model space
            model.append(" ")
        elif r < 0.68:
            # literal newline: a model space, unless it completes
            # a literal CRLF pair, which reads as one space
            if not (toks and toks[-1] == "\r"):
                model.append(" ")
            toks.append("\n")
        elif r < 0.72:
            toks.append("\r")       # literal CR: model space
            model.append(" ")
        elif r < 0.78:
            toks.append("&#9;")
            model.append("\t")
        elif r < 0.82:
            toks.append("&#10;")
            model.append("\n")
        elif r < 0.86:
            toks.append("&#13;")
            model.append("\r")
        elif r < 0.90:
            toks.append("&lt;")
            model.append("<")
        elif r < 0.93:
            toks.append("&amp;")
            model.append("&")
        elif r < 0.96:
            other = "'" if quote == '"' else '"'
            toks.append(other)
            model.append(other)
        else:
            toks.append("&quot;" if quote == '"' else "&apos;")
            model.append(quote)
    return "".join(toks), "".join(model), quote


def join_words(rng, words):
    """Words joined by a space or, now and then, by a line end:
    returns (spelling, model). Words never start with a line
    feed, so a lone carriage return is safe between them."""
    sp = []
    model = []
    for i, w in enumerate(words):
        if i > 0:
            if rng.random() < 0.2:
                sp.append(spell_line_end(rng, None))
                model.append("\n")
            else:
                sp.append(" ")
                model.append(" ")
        sp.append(w)
        model.append(w)
    return "".join(sp), "".join(model)


def gen_comment(rng):
    words = [rng.choice(COMMENT_WORDS)
             for _ in range(rng.randint(0, 4))]
    sp, model = join_words(rng, words)
    body_sp = " " + sp + " " if words else ""
    body = " " + model + " " if words else ""
    if rng.random() < 0.3:
        body_sp = body_sp + "- x "
        body = body + "- x "
    return "<!--" + body_sp + "-->", ("comment", body)


def gen_pi(rng):
    target = gen_name(rng)
    while target.lower() == "xml":
        target = gen_name(rng)
    if rng.random() < 0.35:
        return "<?" + target + "?>", ("pi", target, "")
    words = [rng.choice(COMMENT_WORDS)
             for _ in range(rng.randint(1, 3))]
    sp, data = join_words(rng, words)
    return ("<?" + target + " " + sp + "?>",
            ("pi", target, data))


# Whitespace inside tags and at the top level. A separator before an
# attribute is never empty: XML 1.0 [40] and [44] require one.
SEPS = [" ", " ", " ", "  ", "\t", "\n", " \n\t", "\r\n", "\r"]
OPT_WS = ["", "", "", " ", "\n", "\t ", "\r\n", "\r"]


def gen_sep(rng):
    return rng.choice(SEPS)


def gen_opt_ws(rng):
    return rng.choice(OPT_WS)


def gen_element(rng, depth):
    name = gen_name(rng)
    used = set()
    attrs = []
    attr_spell = []
    for _ in range(rng.randint(0, 3)):
        an = gen_name(rng)
        if an in used or an == "xmlns":
            continue
        used.add(an)
        sp, val, q = gen_attr_value(rng)
        attrs.append((an, val))
        eq = rng.choice(["=", " = ", "= ", " ="])
        attr_spell.append(gen_sep(rng) + an + eq + q + sp + q)
    content = []
    content_spell = []
    if depth < 4:
        for _ in range(rng.randint(0, 4)):
            r = rng.random()
            if r < 0.38:
                sub_sp, sub = gen_element(rng, depth + 1)
                content.append(sub)
                content_spell.append(sub_sp)
            elif r < 0.52:
                sp, node = gen_comment(rng)
                content.append(node)
                content_spell.append(sp)
            elif r < 0.62:
                sp, node = gen_pi(rng)
                content.append(node)
                content_spell.append(sp)
            else:
                sp, model = gen_text_run(rng)
                if content and content[-1][0] == "text":
                    content[-1] = ("text", content[-1][1] + model)
                else:
                    content.append(("text", model))
                content_spell.append(sp)
    model = ("elem", name, attrs, content)
    stag = "<" + name + "".join(attr_spell) + gen_opt_ws(rng)
    etag = "</" + name + gen_opt_ws(rng) + ">"
    if not content:
        if rng.random() < 0.5:
            return stag + "/>", model
        return stag + ">" + etag, model
    return stag + ">" + "".join(content_spell) + etag, model


def gen_document(rng):
    prolog = []
    prolog_spell = []
    for _ in range(rng.randint(0, 2)):
        if rng.random() < 0.5:
            sp, node = gen_comment(rng)
        else:
            sp, node = gen_pi(rng)
        prolog.append(node)
        prolog_spell.append(sp)
    root_sp, root = gen_element(rng, 0)
    epilog = []
    epilog_spell = []
    for _ in range(rng.randint(0, 2)):
        if rng.random() < 0.5:
            sp, node = gen_comment(rng)
        else:
            sp, node = gen_pi(rng)
        epilog.append(node)
        epilog_spell.append(sp)
    text = (gen_opt_ws(rng)
            + "".join(sp + gen_opt_ws(rng) for sp in prolog_spell)
            + root_sp
            + "".join(gen_opt_ws(rng) + sp for sp in epilog_spell)
            + gen_opt_ws(rng))
    return text, (prolog, root, epilog)


# ----------------------------------------------------------------


def lake_env():
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env["PATH"]
    return env


def build_exe():
    """Always run `lake build`: it does nothing when the build is
    current, and rebuilds the tool after a source change, so a stale
    binary is never tested."""
    out = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True,
                         text=True, timeout=BUILD_TIMEOUT, env=lake_env())
    if out.returncode != 0:
        sys.stderr.write(out.stdout + out.stderr)
        raise SystemExit("lake build failed with status %d"
                         % out.returncode)


def lean_version():
    out = subprocess.run(["lean", "--version"], capture_output=True,
                         text=True, timeout=60, cwd=ROOT, env=lake_env())
    return out.stdout.strip() or "unknown"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=SEED_DEFAULT)
    ap.add_argument("--count", type=int, default=COUNT_DEFAULT)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    build_exe()
    failures = []

    # Part 1: fixed cases.
    inputs = [t for t, _ in FIXED]
    answers = run_requests(inputs, failures, "fixed cases")
    fixed_answers = answers
    fixed_ok = 0
    for (text, expected), ans in zip(FIXED, answers):
        want = "ok:" + codes(expected)
        if ans == want:
            fixed_ok += 1
        else:
            failures.append("fixed case %r: got %r, want %r"
                            % (text, ans, want))

    # Part 2: generated differential. Every failing document is
    # counted; only the printed list is cut short.
    gen_inputs = []
    gen_docs = []
    for _ in range(args.count):
        text, doc = gen_document(rng)
        gen_inputs.append(text)
        gen_docs.append(doc)
    answers = run_requests(gen_inputs, failures, "generated")
    gen_answers = answers
    gen_ok = 0
    et_ok = 0
    for text, doc, ans in zip(gen_inputs, gen_docs, answers):
        want = "ok:" + codes(print_doc(doc))
        why = []
        if ans != want:
            why.append("tool answered %r" % (ans[:120],))
        try:
            et_root = et_parse(text)
            if et_to_model(et_root) != doc[1]:
                why.append("ElementTree read a different tree")
            else:
                et_ok += 1
            et_canon = et_parse(print_doc(doc))
            if et_to_model(et_canon) != doc[1]:
                why.append("ElementTree read a different tree "
                           "from the canonical print")
        except ET.ParseError as e:
            why.append("ElementTree rejected it: %s" % e)
        if why:
            failures.append("generated %r: %s" % (text, "; ".join(why)))
        else:
            gen_ok += 1

    # Part 3: print then parse. Every canonical print the tool gave
    # in parts 1 and 2 is sent back; the answer must be the same
    # print (Spec.print_parse, run on the compiled tool).
    printed = []
    for ans in fixed_answers + gen_answers:
        if ans.startswith("ok:") and len(ans) > 3:
            printed.append("".join(chr(int(x)) for x in ans[3:].split(",")))
    re_answers = run_requests(printed, failures, "print then parse")
    reprint_ok = 0
    for text, ans in zip(printed, re_answers):
        if ans == "ok:" + codes(text):
            reprint_ok += 1
        else:
            failures.append("print then parse %r: got %r" % (text, ans[:120]))

    # Part 4: named rejections. Also record ElementTree's verdict
    # on each: accepted means an out of subset disagreement.
    rej_inputs = [t for _, t in REJECTIONS]
    answers = run_requests(rej_inputs, failures, "named rejections")
    rej_ok = 0
    oos = []
    for (rule, text), ans in zip(REJECTIONS, answers):
        if ans == "none":
            rej_ok += 1
        else:
            failures.append("rejection %s: tool answered %r for %r"
                            % (rule, ans, text))
        try:
            et_parse(text)
            oos.append(rule)
        except ET.ParseError:
            pass

    # Malformed requests.
    bad_answers = run_tool(MALFORMED, failures, "malformed requests")
    bad_ok = 0
    for line, ans in zip(MALFORMED, bad_answers):
        if ans == "error":
            bad_ok += 1
        else:
            failures.append("malformed %r: got %r, want error"
                            % (line, ans))
    empty_ans = run_tool(["parse", "parse "], failures, "bare parse")
    if empty_ans != ["none", "none"]:
        failures.append("bare 'parse' answered %r, want two nones"
                        % (empty_ans,))

    lines = []
    lines.append("# Test results")
    lines.append("")
    lines.append("Written by `tests/run_tests.py`. Rerun it to "
                 "check these numbers.")
    lines.append("")
    total = (len(FIXED) + len(gen_inputs) + len(printed)
             + len(REJECTIONS) + len(MALFORMED) + 2)
    lines.append("- Oracle: Python %s `xml.etree.ElementTree`, "
                 "%s (`ET.XMLParser`, which turns namespace "
                 "processing on, with a `TreeBuilder` that keeps "
                 "comments and processing instructions)"
                 % (sys.version.split()[0], pyexpat.EXPAT_VERSION))
    lines.append("- Lean tool: %s" % lean_version())
    lines.append("- Seed: %d" % args.seed)
    lines.append("- Inputs: %d" % total)
    lines.append("  - every request sent to the tool: the fixed cases, "
                 "the generated documents, the canonical prints sent "
                 "back, the named rejections, the malformed requests, "
                 "and two bare parse requests")
    lines.append("- Fixed cases passed: %d of %d"
                 % (fixed_ok, len(FIXED)))
    lines.append("- Generated in-subset documents: %d" % len(gen_inputs))
    lines.append("- Generated documents where the tool's canonical "
                 "print matches the tree and ElementTree agrees on "
                 "the tree: %d" % gen_ok)
    lines.append("- ElementTree tree agreements on generated "
                 "documents: %d" % et_ok)
    lines.append("- Canonical prints that parse back to the same "
                 "print: %d of %d" % (reprint_ok, len(printed)))
    lines.append("- Named rejections rejected by the tool: %d of %d"
                 % (rej_ok, len(REJECTIONS)))
    lines.append("- Out of subset disagreements (ElementTree "
                 "accepts, this slice rejects, by design): %d"
                 % len(oos))
    for rule in oos:
        lines.append("  - %s" % rule)
    lines.append("- Malformed requests answered error: %d of %d"
                 % (bad_ok, len(MALFORMED)))
    lines.append("- Bare parse requests answered none: %s"
                 % ("yes" if empty_ans == ["none", "none"] else "no"))
    lines.append("- Failures: %d" % len(failures))
    for f in failures[:40]:
        lines.append("  - %s" % f)
    if len(failures) > 40:
        lines.append("  - (%d more not shown)" % (len(failures) - 40))
    RESULTS.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
