# xml: an XML safe-subset parser and printer, with a proved round trip

Status: in progress

A parser and printer in Lean for a safe subset of XML 1.0:
elements, attributes, text, comments, processing
instructions, character references, and CDATA sections,
with one root element. There is no document type
declaration, no entity declarations, no namespaces, and
no XML declaration in the subset; the parser rejects a
document with any of those rather than parsing it
leniently. "What is proved" below says which of these
rejections are theorems, and for which texts; the tests
check the rest. The definitions are in `Xml/Value.lean`
(the tree type, the printer, and the well-formedness
rules) and `Xml/Parse.lean` (the parser). The proofs are
in `Proofs/`: the round trip in `RoundTrip.lean`, well
formedness of every accepted document in `ParseWF.lean`,
line ends in `LineEnds.lean`, and the refused texts in
`Refusals.lean`. The full subset rules are in `SPEC.md`.

The statements a reviewer approves are in `Spec.lean`,
with their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

Needs Linux and [elan](https://github.com/leanprover/elan).
`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line:
the word `parse`, a space, and the text as
comma-separated decimal character codes. It answers
`ok:` and the character codes of the canonical print
when the text parses, `none` when it is rejected, and
`error` when the request itself is malformed.

```
echo "parse 60,97,47,62" | .lake/build/bin/xml
```

That request is the text `<a/>`, and the answer is
`ok:60,97,47,62`. See `SPEC.md` for the full protocol.

`python3 tests/run_tests.py` runs `lake build` (which
does nothing when the build is current), runs the fixed
cases, and runs the differential tests against Python's
`xml.etree.ElementTree` with a fixed seed, writing the
counts to `tests/TEST-RESULTS.md`. ElementTree has no
subset setting: it is the stock parser, with namespace
processing on, so documents outside the subset are told
apart by the harness's named rejection list and counted
apart, not by the oracle.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

The first five hold for every text or every well formed
document. The refusals after them are each about a family
of texts, and each row says which family. Most families
share a shape: a well formed prolog (comments and
processing instructions, as `Xml.WF` allows them),
printed in canonical form; then, for most, the root's
start tag with any valid name and any well formed
attributes, also printed; then the form the rule turns
away; then anything at all. "Printed" means written the
way `Xml.print` writes it.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed document gives the document back. | `Spec.parse_print` |
| Every text the parser accepts gives a well formed document (`Xml.WF`, described below): among other things, no name anywhere in the tree holds a colon or starts with a digit, no attribute name stands twice on one element and none is `xmlns`, every character is a legal XML character, and comment bodies hold no `--`. | `Spec.parse_wf` |
| Printing a document the parser accepted gives a text that parses back to the same document (the plan's main claim, as written). | `Spec.print_parse` |
| A carriage return followed by a line feed reads exactly as one line feed, anywhere in a text, unless the text before it ends with a carriage return (XML 1.0 section 2.11). | `Spec.crlf_reads_as_lf` |
| A carriage return not followed by a line feed reads exactly as a line feed, anywhere in a text, unless the text before it ends with a carriage return. | `Spec.cr_reads_as_lf` |
| After a printed prolog, `<!DOCTYPE` and anything after it is refused. | `Spec.rejects_doctype` |
| After a printed prolog, `<![CDATA[` and anything after it is refused. | `Spec.rejects_cdata_in_prolog` |
| A text that starts with `<?` and a target that is the word `xml` in any letter case (the XML declaration form), then anything that does not make the target longer, is refused. | `Spec.rejects_xml_declaration` |
| After a printed prolog, a character that is neither whitespace nor `<`, then anything, is refused (character data before the root). | `Spec.rejects_text_before_root` |
| Any well formed document, printed, followed by `<` and a name start character, then anything, is refused (a second root). | `Spec.rejects_second_root` |
| After a printed prolog, `<` and one of the ten digits, then anything, is refused (an element name cannot start with a digit). | `Spec.rejects_digit_name` |
| After a printed prolog, `<`, any valid name and a colon, then anything, is refused (no colon in the root's name). | `Spec.rejects_colon_in_name` |
| After a printed prolog, a well formed root element written as its printed start tag, its printed content and an end tag that names a different valid name, then anything, is refused. | `Spec.rejects_mismatched_tags` |
| After a printed prolog, the root's printed start tag at the very end of the text is refused (an element with no end tag). | `Spec.rejects_unclosed_element` |
| In the root's first run of character data (after a printed prolog and the root's printed start tag, then any text with no `<` and no `&`), a reference `&name;` to any valid name other than `lt`, `gt`, `amp`, `apos` and `quot` is refused, whatever follows: no such entity is expanded there. | `Spec.rejects_undefined_entity` |
| The same in an attribute value of the root: after the root's printed attributes, a space, a valid attribute name, `="`, any text with no `"` and no `&`, then `&name;` for a valid name other than the five, whatever follows. | `Spec.rejects_undefined_entity_in_attribute` |
| In the root's first run of character data, as above, the reference `&#xD800;` (a surrogate) is refused, whatever follows. | `Spec.rejects_surrogate_ref` |
| In the same place, the reference `&#0;` is refused, whatever follows. | `Spec.rejects_zero_ref` |
| In the same place, the run `]]>` is refused, whatever follows. | `Spec.rejects_cdata_close_in_text` |
| For a comment that is the root's first content: `<!--`, a body a well formed comment may hold, `--`, then any character but `>` is refused, whatever follows. | `Spec.rejects_dashdash_in_comment` |
| On the root, after its printed attributes: one more printed attribute whose name is already among them, with any value, is refused, whatever follows. | `Spec.rejects_duplicate_attribute` |
| On the root, after its printed attributes: a space, a valid attribute name, `="`, any text with no `"` and no `&`, then a raw `<`, is refused, whatever follows. | `Spec.rejects_lt_in_attribute` |
| On the root, after its printed attributes: a space, a valid attribute name, `=`, then a character that is no quote and no whitespace, is refused, whatever follows. | `Spec.rejects_unquoted_attribute` |
| On the root, after at least one printed attribute: a name start character right after the closing quote, with no whitespace between, is refused, whatever follows (XML 1.0 productions [40] and [44]). | `Spec.rejects_attribute_without_space` |
| On the root, after its printed attributes: a space and an attribute named `xmlns` (a default namespace declaration) are refused, whatever follows the name that does not make it longer. | `Spec.rejects_xmlns` |

A document is well formed when its names match the
subset's name rule, attribute names are unique per
element and none is `xmlns`, text holds only legal XML
characters and no two text runs stand next to each
other, comment bodies contain no `--`, do not end with
`-` and hold no carriage return, processing instruction
targets are valid and not the reserved word `xml` and
their data holds no carriage return, and the prolog and
epilog hold only comments and processing instructions.
`SPEC.md` states the rules in full. Because
`Spec.parse_wf` holds for every text, these properties
hold anywhere in any accepted tree, not only at the
root.

The parser normalizes line ends before it reads, as
XML 1.0 section 2.11 requires: a carriage return and
line feed pair, and a lone carriage return, each read as
one line feed. A carriage return written as `&#13;` in
text or an attribute value reads as itself, and the
printer writes it that way.

A parser that refuses every text meets every statement
above except `Spec.parse_print`, which rules it out.

The proofs use no axiom but the three standard ones
(`propext`, `Classical.choice`, `Quot.sound`):
`comparator.json` names those three as the permitted
axioms, and `lake comparator` checks each proof in
`Proofs/SpecProofs.lean` against its statement in
`Spec.lean` and against that list, under all six kernels
shipped with Lean.

The command line tool in `Main.lean` calls `Xml.parse`
and `Xml.print` directly, the same functions the theorems
are about.

## What is not proved

- That the tree the parser gives is the right reading of
  the text. `Spec.parse_wf` says the tree is well formed
  and `Spec.print_parse` that it survives printing, but
  neither ties the tree to the text it came from: a parser
  that read `&e;` as some character, or dropped an
  attribute, would meet both. The differential tests check
  the reading against ElementTree instead.
- That the parser rejects every text the subset forbids.
  Each refusal theorem covers the family its row names and
  no other position. For example, a reference to an
  undefined entity is proved refused in the root's first
  run of character data and in an attribute value of the
  root, but not inside a nested element or after other
  markup; a duplicate or unquoted attribute is proved
  refused on the root only; an unclosed element only when
  its start tag ends the text; a document type
  declaration only right after the prolog. So "no entity
  is ever expanded" is a theorem only in those positions.
  The parser does reject the other positions too, and the
  named rejections in the tests check many of them, but
  that is testing, not proof.
- That the parser accepts every text the subset allows.
  The round trip shows it accepts every canonical print;
  other spellings rest on the tests.
- Anything about documents outside the subset: documents
  with a document type declaration, entities beyond the
  five predefined ones, namespaces, an XML declaration,
  or non-ASCII names. Whether a full XML parser would
  accept them is not a claim here.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser, and the check that
  a code is a Unicode scalar value. The tests cover them,
  malformed requests included.
- Speed. The code works on lists of characters, which
  suits proofs, not large data. The parser's fuel is the
  length of the input text, which very deep inputs can
  reach.

Two deliberate choices, also stated in `SPEC.md`:

- CDATA sections are a spelling, not a tree difference.
  CDATA content becomes ordinary character data in the
  same text node stream, and the printer never writes a
  CDATA section. The claim is at tree level, so this is
  sound.
- The XML declaration is not in the model. A processing
  instruction target of `xml` in any letter case rejects
  everywhere, which keeps the declaration out.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, which turns the proved definitions
  into the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- That `SPEC.md` states the reading of XML 1.0 you
  intend. The proofs are about the parser and printer in
  this repo following each other exactly; the fidelity of
  the spec to XML 1.0 is a reading, pinned in SPEC.md
  where the standard leaves a choice open.
- Python's standard library, as the oracle in the
  differential tests. The results file names the version
  used. The plan also names Go's encoding/xml and Rust's
  quick-xml as oracles; neither is wired in yet, and the
  harness says so rather than counting them.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   named rejections, and the differential run against
   Python's `xml.etree.ElementTree`, with counts and any
   failures written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean.
