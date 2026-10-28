# xml: an XML safe-subset parser and printer, with a proved round trip

Status: in-progress

A parser and printer in Lean for a safe subset of XML 1.0:
elements, attributes, text, comments, processing
instructions, character references, and CDATA sections,
with one root element. There is no document type
declaration, no entity declarations, no namespaces, and
no XML declaration in the subset; a document with any of
those is rejected, not parsed leniently. The definitions
are in `Xml/Value.lean` (the tree type, the printer, and
the well-formedness rules) and `Xml/Parse.lean` (the
parser). The proofs are in `Proofs/RoundTrip.lean`. The
full subset rules are in `SPEC.md`.

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

`python3 tests/run_tests.py` rebuilds the tool if needed,
runs the fixed cases, and runs the differential tests
against Python's `xml.etree.ElementTree` in subset mode
with a fixed seed, writing the counts to
`tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed document gives the document back. | `Spec.parse_print` |
| A document carrying a document type declaration is refused. | `Spec.rejects_doctype` |
| A reference to an entity the subset does not define is refused. | `Spec.rejects_undefined_entity` |
| An end tag that does not match the start tag is refused. | `Spec.rejects_mismatched_tags` |
| An element with no end tag is refused. | `Spec.rejects_unclosed_element` |
| A second root element is refused. | `Spec.rejects_second_root` |
| Character data before the root element is refused. | `Spec.rejects_text_before_root` |
| An attribute name standing twice on one element is refused. | `Spec.rejects_duplicate_attribute` |
| A raw less sign inside an attribute value is refused. | `Spec.rejects_lt_in_attribute` |
| The run `]]>` inside text is refused. | `Spec.rejects_cdata_close_in_text` |
| Two dashes in a row inside a comment body are refused. | `Spec.rejects_dashdash_in_comment` |
| A character reference naming a surrogate value is refused. | `Spec.rejects_surrogate_ref` |
| A character reference naming zero is refused. | `Spec.rejects_zero_ref` |
| A colon in a name is refused. | `Spec.rejects_colon_in_name` |
| A name starting with a digit is refused. | `Spec.rejects_digit_name` |
| An attribute value with no quotes is refused. | `Spec.rejects_unquoted_attribute` |
| A CDATA section in the prolog is refused. | `Spec.rejects_cdata_in_prolog` |
| The XML declaration form is refused. | `Spec.rejects_xml_declaration` |

A document is well formed when its names match the
subset's name rule, attribute names are unique per
element, text holds only legal XML characters and no two
text runs stand next to each other, comment bodies
contain no `--` and do not end with `-`, processing
instruction targets are valid and not the reserved word
`xml`, and the prolog and epilog hold only comments and
processing instructions. `SPEC.md` states the rules in
full.

The round trip theorem rests on the proof in
`Proofs/RoundTrip.lean`, where it is
`Xml.Proofs.parse_print`. It uses no axiom but the three
standard ones (`propext`, `Classical.choice`,
`Quot.sound`): `comparator.json` names those three as the
permitted axioms, and `lake comparator` checks each proof
in `Proofs/SpecProofs.lean` against its statement in
`Spec.lean` and against that list. The refusal theorems
are single inputs checked in the kernel with
`decide +kernel`.

The command line tool in `Main.lean` calls `Xml.parse`
and `Xml.print` directly, the same functions the theorems
are about.

## What is not proved

- That the parser accepts every text the subset allows,
  and rejects every text it forbids. The round trip does
  not need either, and the refusal theorems pin single
  inputs only, so neither holds in general as a proof.
  The differential tests check that behaviour instead,
  and the results file records the outcome, including any
  failure.
- Anything about documents outside the subset: documents
  with a document type declaration, entities beyond the
  five predefined ones, namespaces, an XML declaration,
  or non-ASCII names. The parser rejects them; whether a
  full XML parser would accept them is not a claim here.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser, and the check that
  a code is a Unicode scalar value. The tests cover them,
  malformed requests included.
- Speed. The code works on lists of characters, which
  suits proofs, not large data. The parser's fuel is the
  length of the input text, which very deep inputs can
  reach.

Three deliberate choices, also stated in `SPEC.md`:

- CDATA sections are a spelling, not a tree difference.
  CDATA content becomes ordinary character data in the
  same text node stream, and the printer never writes a
  CDATA section. The claim is at tree level, so this is
  sound.
- There is no line ending normalization in text,
  comments, processing instruction data, or CDATA: a
  literal carriage return reads as itself. Full XML
  normalizes it to a line feed. Inside attribute values
  both readings agree (either form reads as a space), and
  the printer always writes a carriage return as a
  character reference.
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
