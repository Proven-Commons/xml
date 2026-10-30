# Specification: xml

A parser and printer in Lean for a safe subset of XML 1.0 (Fifth
Edition), narrowed as stated here. A reviewer who did not write
this specification approves it, together with the statement file
`Xml/Spec.lean`. No reviewer has approved them yet, so nothing here
counts toward the verified bar yet.

Text is `List Char`. A Lean `Char` is one Unicode scalar value.

The rules below say what the parser and printer must do.
Which of them are theorems, and for which texts, is listed
under "Properties and their theorems"; the tests in `tests/`
check the rest.

## Line ends

Before anything else, the parser normalizes line ends, as XML 1.0
section 2.11 requires: a carriage return followed by a line feed
becomes one line feed, and a carriage return followed by anything
else, or by nothing, becomes a line feed. This holds everywhere:
in text, CDATA sections, comments, processing instruction data,
attribute values, tags, and between the top level items. So a
literal carriage return never reaches the tree. A carriage return
written as the character reference `&#13;` or `&#xD;` in text or
in an attribute value reads as itself, and the printer writes a
carriage return in text or an attribute value as `&#13;`, the only
way to keep one. A comment or a processing instruction has no
references, so it never holds a carriage return.

## The subset in one paragraph

A document is a prolog of comments and processing instructions,
one root element, and an epilog of comments and processing
instructions. There is no XML declaration, no document type
declaration, no entity declarations, and no namespaces. The only
entity references are the five predefined ones, plus character
references. Anything outside the rules below is rejected, never
parsed leniently.

## Documents

- The prolog and the epilog hold only comments and processing
  instructions, with whitespace allowed between them and around
  the root. Any other text at the top level (character data, a
  second element, a document type declaration, a CDATA section)
  rejects.
- There is exactly one root element.
- The XML declaration is not part of this subset. A processing
  instruction whose target is `xml`, in any letter case, rejects
  everywhere, which keeps the declaration form (`<?xml ...?>`)
  out. A producer that writes a declaration can be asked for the
  same document without it. Other targets that merely start with
  the letters xml, such as `xml-stylesheet`, are ordinary
  processing instructions.

## Names

- A name starts with an ASCII letter (A to Z, a to z) or an
  underscore.
- Later characters may also be ASCII digits, a hyphen, or a dot.
- A colon is never allowed in a name in this subset. In XML a
  colon signals namespace use, and namespaces are out. The colon
  rule alone does not keep namespaces out, because a default
  namespace is declared with the plain name `xmlns`; see the
  attribute rules below.
- Non-ASCII names are out of the subset. XML 1.0 allows far
  more; that is later work, not this slice.

## Elements and attributes

- An element is a name, attributes, and either an empty element
  tag (`<a/>`) or content and a matching end tag (`<a>...</a>`).
  Mismatched tags reject.
- An attribute is a name, an equals sign, and a quoted value.
  Single and double quotes are both read; the printer writes
  double quotes.
- A duplicate attribute name on one element rejects.
- An attribute named `xmlns` rejects. In Namespaces in XML 1.0
  it declares a default namespace (`DefaultAttName ::= 'xmlns'`),
  which namespace-aware parsers apply to the element's name and
  its children's names, so accepting it as an ordinary attribute
  would read a different tree from theirs. Only that exact name
  is refused: `xmlnsx`, `XMLNS`, and an element named `xmlns`
  declare nothing and are ordinary names. A prefixed declaration
  (`xmlns:p`) rejects by the colon rule.
- Whitespace (space, tab, line feed, carriage return) must stand
  before each attribute, as XML 1.0 requires (`(S Attribute)*` in
  productions [40] and [44]): an attribute name that starts right
  after the closing quote of the one before it rejects, as in
  `<a b="1"c="2"/>`. Whitespace may also appear around the equals
  sign, and before the closing bracket of a start tag or an end
  tag.
- In an attribute value: character references and the five
  predefined entities are expanded on read. A raw `<` rejects.
  A raw `&` that does not begin a valid reference rejects.
- Attribute value normalization: a literal tab or line feed in
  a value reads as one space. A literal carriage return, alone or
  before a line feed, has already become one line feed (see Line
  ends), so it reads as one space too. This is
  XML's rule for CDATA type attributes, and every attribute here
  is CDATA type because there is no document type declaration
  to say otherwise. A tab or line feed spelled as a character
  reference is not normalized; it reads as itself. The model
  holds the normalized value, so printing and reparsing is
  stable.

## Text

- Character data runs between markup. A raw `<` begins markup,
  never text. A raw `&` must begin a valid reference.
- The five predefined entities decode: `&lt;`, `&gt;`, `&amp;`,
  `&apos;`, `&quot;`. Any other entity reference rejects,
  because no entities exist in the subset.
- A character reference (`&#65;` decimal, `&#x41;` hex; the x is
  lowercase only) decodes to its character. The value must be a
  legal XML character: tab, line feed, carriage return, 0x20 to
  0xD7FF, 0xE000 to 0xFFFD, or 0x10000 to 0x10FFFF. Anything
  else (zero, a control character, a surrogate value, a value
  past 0x10FFFF) rejects.
- A raw character in text, a comment, a processing instruction,
  a CDATA section, or an attribute value must also be a legal
  XML character, or the text rejects.
- The sequence `]]>` inside text rejects, as XML requires
  outside a CDATA section.
- Adjacent character data merges into one text node in the
  model: plain text, character references, and CDATA sections
  between two markup items form a single run. The printer
  writes one run, and the round trip claim is about this merged
  tree.

## CDATA sections

- A CDATA section (`<![CDATA[ ... ]]>`) may appear inside
  element content only, never in the prolog or the epilog.
- The text inside is literal. In the model it becomes ordinary
  character data in the same text node stream as its neighbours.
  CDATA is a spelling, not a tree difference, exactly as the
  choice of quote in an attribute is a spelling. The printer
  never writes a CDATA section.

## Comments

- A comment is `<!--`, a body, and `-->`. The body must not
  contain `--` and must not end with `-`. Both are XML's rules,
  and they keep the closing marks unambiguous.
- The body is carried as the characters between the marks.
- A comment may appear in the prolog, in content, or in the
  epilog, and is a node in place.

## Processing instructions

- A processing instruction is `<?`, a target name (the name
  rule above), and then either the closing marks `?>` at once,
  or whitespace and data up to `?>`.
- The target `xml` in any letter case is reserved and rejects
  (see Documents).
- The data is carried as text. It may be empty. It must not
  contain `?>`, and in the model it never starts with
  whitespace: the whitespace after the target is a separator,
  not part of the data.

## Document type declarations and other `<!` forms

- Any `<!DOCTYPE`, anywhere, rejects.
- The same door rejects every other `<!` form that is not a
  comment or (inside content) a CDATA section: `<!ENTITY`,
  `<!ELEMENT`, and the rest. There are no declarations of any
  kind in this subset, so the parser must never expand an
  entity beyond the five predefined ones. This is a rule, and
  only part of it is a theorem: under Properties and their
  theorems, `Xml.Spec.rejects_undefined_entity` covers the root's
  first run of character data and
  `Xml.Spec.rejects_undefined_entity_in_attribute` the root's
  attribute values. Every other position, a nested element
  among them, rests on the tests.

## Printing

The printer writes one canonical form:

- Elements print with attributes in model order, values in
  double quotes. An element with no content prints in the short
  form `<a/>`. An element read from `<a></a>` has no content
  and also prints as `<a/>`: same tree, different spelling.
- In text: `&` as `&amp;`, `<` as `&lt;`, `>` as `&gt;` (always
  escaping `>` keeps `]]>` from ever forming in printed text),
  and carriage return as `&#13;`. Every other character prints
  as itself.
- In attribute values: `&` as `&amp;`, `<` as `&lt;`, `"` as
  `&quot;`, and tab, line feed, and carriage return as
  `&#9;`, `&#10;`, `&#13;`. A literal tab in a printed value
  would read back as a space under normalization, so character
  references are how those characters are kept.
- A processing instruction with no data prints as `<?target?>`;
  with data, as `<?target data?>` with one space.
- A document prints as its prolog, its root, and its epilog,
  with nothing between them.

## Well formed trees

The round trip is claimed for trees that satisfy a well
formedness predicate (`WF` in `Xml/Value.lean`):

- every name matches the name rule above;
- attribute names are unique per element and none is `xmlns`,
  and attribute values hold only legal XML characters;
- text nodes are not empty, hold only legal XML characters,
  and two text nodes never stand next to each other (the
  parser merges them, so an unmerged tree could not come
  back);
- comment bodies hold only legal characters, contain no `--`,
  do not end with `-`, and hold no carriage return;
- processing instruction targets are valid names and not the
  reserved word, their data holds only legal characters, never
  contains `?>`, never starts with whitespace, and holds no
  carriage return;
- the root is an element, and the prolog and epilog hold only
  comments and processing instructions.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem, with the same words there. The theorems
are stated in `Xml/Spec.lean` and proved in
`Xml/Proofs/SpecProofs.lean`, under the same names.

The first five hold for every text or every well formed
document. Each refusal after them is about a family of
texts, and its row says which. Most families share a
shape: a well formed prolog (`MiscOk`), printed in canonical
form; then, for most, the root's start tag with any valid
name and any attributes that meet `AttrsOk`, also printed;
then the form the rule turns away; then anything. No
refusal statement covers its rule in every position: the
rows say where. The tests in `tests/` check the other
positions.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed document gives the document back | `Xml.Spec.parse_print` |
| Every text the parser accepts gives a well formed document (`Xml.WF`, described below): among other things, no name anywhere in the tree holds a colon or starts with a digit, no attribute name stands twice on one element and none is `xmlns`, every character is a legal XML character, and comment bodies hold no `--` | `Xml.Spec.parse_wf` |
| Printing a document the parser accepted gives a text that parses back to the same document (the plan's main claim, as written) | `Xml.Spec.print_parse` |
| A carriage return followed by a line feed reads exactly as one line feed, anywhere in a text, unless the text before it ends with a carriage return (XML 1.0 section 2.11) | `Xml.Spec.crlf_reads_as_lf` |
| A carriage return not followed by a line feed reads exactly as a line feed, anywhere in a text, unless the text before it ends with a carriage return | `Xml.Spec.cr_reads_as_lf` |
| After a printed prolog, `<!DOCTYPE` and anything after it is refused | `Xml.Spec.rejects_doctype` |
| After a printed prolog, `<![CDATA[` and anything after it is refused | `Xml.Spec.rejects_cdata_in_prolog` |
| A text that starts with `<?` and a target that is the word `xml` in any letter case (the XML declaration form), then anything that does not make the target longer, is refused | `Xml.Spec.rejects_xml_declaration` |
| After a printed prolog, a character that is neither whitespace nor `<`, then anything, is refused (character data before the root) | `Xml.Spec.rejects_text_before_root` |
| Any well formed document, printed, followed by `<` and a name start character, then anything, is refused (a second root) | `Xml.Spec.rejects_second_root` |
| After a printed prolog, `<` and one of the ten digits, then anything, is refused (an element name cannot start with a digit) | `Xml.Spec.rejects_digit_name` |
| After a printed prolog, `<`, any valid name and a colon, then anything, is refused (no colon in the root's name) | `Xml.Spec.rejects_colon_in_name` |
| After a printed prolog, a well formed root element written as its printed start tag, its printed content and an end tag that names a different valid name, then anything, is refused | `Xml.Spec.rejects_mismatched_tags` |
| After a printed prolog, the root's printed start tag at the very end of the text is refused (an element with no end tag) | `Xml.Spec.rejects_unclosed_element` |
| In the root's first run of character data (after a printed prolog and the root's printed start tag, then any text with no `<` and no `&`), a reference `&name;` to any valid name other than `lt`, `gt`, `amp`, `apos` and `quot` is refused, whatever follows: no such entity is expanded there | `Xml.Spec.rejects_undefined_entity` |
| The same in an attribute value of the root: after the root's printed attributes, a space, a valid attribute name, `="`, any text with no `"` and no `&`, then `&name;` for a valid name other than the five, whatever follows | `Xml.Spec.rejects_undefined_entity_in_attribute` |
| In the root's first run of character data, as above, the reference `&#xD800;` (a surrogate) is refused, whatever follows | `Xml.Spec.rejects_surrogate_ref` |
| In the same place, the reference `&#0;` is refused, whatever follows | `Xml.Spec.rejects_zero_ref` |
| In the same place, the run `]]>` is refused, whatever follows | `Xml.Spec.rejects_cdata_close_in_text` |
| For a comment that is the root's first content: `<!--`, a body a well formed comment may hold, `--`, then any character but `>` is refused, whatever follows | `Xml.Spec.rejects_dashdash_in_comment` |
| On the root, after its printed attributes: one more printed attribute whose name is already among them, with any value, is refused, whatever follows | `Xml.Spec.rejects_duplicate_attribute` |
| On the root, after its printed attributes: a space, a valid attribute name, `="`, any text with no `"` and no `&`, then a raw `<`, is refused, whatever follows | `Xml.Spec.rejects_lt_in_attribute` |
| On the root, after its printed attributes: a space, a valid attribute name, `=`, then a character that is no quote and no whitespace, is refused, whatever follows | `Xml.Spec.rejects_unquoted_attribute` |
| On the root, after at least one printed attribute: a name start character right after the closing quote, with no whitespace between, is refused, whatever follows (XML 1.0 productions [40] and [44]) | `Xml.Spec.rejects_attribute_without_space` |
| On the root, after its printed attributes: a space and an attribute named `xmlns` (a default namespace declaration) are refused, whatever follows the name that does not make it longer | `Xml.Spec.rejects_xmlns` |

`Xml.Spec.parse_wf` holds for every text: whatever the parser
accepts meets every rule under Well formed trees, anywhere in
the tree. With the round trip it gives `Xml.Spec.print_parse`, the
plan's main claim as written. Neither says that the tree is
the right reading of the text: that rests on the tests. A
parser that refuses every text meets every statement in the
table except `Xml.Spec.parse_print`, which is the statement such a
parser fails. The proof of `Xml.Spec.parse_wf` is
`Xml.Proofs.parse_wf` in `Xml/Proofs/ParseWF.lean`; the line end
statements are proved in `Xml/Proofs/LineEnds.lean`, and the
refusals in `Xml/Proofs/Refusals.lean`.

The round trip behind `Xml.Spec.parse_print` is
`Xml.Proofs.parse_print` in `Xml/Proofs/RoundTrip.lean`. Its
proofs rest on helper round trips proved in the same file:
one element and a list of content nodes together
(`Xml.Proofs.elem_nodes`), a prolog or epilog list
(`Xml.Proofs.parseMisc_print`), a printed comment body
(`Xml.Proofs.parseCommentBody_print`), a printed
processing instruction (`Xml.Proofs.parsePI_print`), and
escaped text and attribute values read back
(`Xml.Proofs.parseCharData_escapeText`,
`Xml.Proofs.parseAttrValue_escapeAttr`). Each proof in
`Xml/Proofs/SpecProofs.lean` uses no axiom but the three
standard ones (`propext`, `Classical.choice`,
`Quot.sound`): `comparator.json` names those three as the
permitted axioms, and `lake comparator` checks the proofs
against that list, under all six kernels shipped with Lean.

## Boundaries and named differences

- No document type declaration, no entities beyond the five,
  no namespaces, no XML declaration, ASCII names only. A full
  XML parser may accept documents this slice rejects for
  exactly those reasons; the test harness counts those as out
  of subset disagreements, not failures.
- ElementTree, the one oracle wired into the tests, drops the
  prolog and epilog when it reads a document, so the harness
  compares ElementTree's tree for the root element and checks
  the prolog and epilog through the canonical print. The plan
  also names Go's encoding/xml and Rust's quick-xml as oracles;
  neither is wired in yet, and the harness says so rather than
  counting them.

## The request protocol

The command line tool in `Main.lean` reads one request per
line and prints one answer per line. A request is the operation
`parse`, then one space, then the input as comma-separated
decimal character codes. The answer is `ok:` and the character
codes of the canonical print, `none` when the text is
rejected, and `error` when the request itself is malformed (an
unknown operation, a number that is not plain decimal digits,
or a code that is not a Unicode scalar value). A request with
no codes is the empty input, which answers `none`. A line may
end in LF or CR LF.
