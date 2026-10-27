# xml: an XML safe-subset parser and printer, with a proved round trip

A parser and printer in Lean for a safe subset of XML 1.0: elements, attributes, text, comments, processing instructions, character references, and CDATA sections, with one root element. There is no document type declaration, no entity declarations, no namespaces, and no XML declaration in the subset; a document with any of those is rejected, not parsed leniently. The printer writes one canonical form. The main claim is proved: printing a well formed document gives a text that parses to the same document. The tests run the parser against Python's `xml.etree.ElementTree` in subset mode; see `tests/TEST-RESULTS.md` for the counts. The full subset rules are in `SPEC.md`.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## What is proved

The definitions are in `Xml/Value.lean` (the tree type, the printer, and the well-formedness rules) and `Xml/Parse.lean` (the parser). The proofs are in `Proofs/RoundTrip.lean`.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed document gives the document back. | `Xml.Proofs.parse_print` |
| The same for one element and for a list of content nodes, proved together by strong induction on the length of the printed form. | `Xml.Proofs.elem_nodes` |
| The same for a prolog or epilog list of comments and processing instructions. | `Xml.Proofs.parseMisc_print` |
| Reading back a printed comment body gives the body back. | `Xml.Proofs.parseCommentBody_print` |
| Reading back a printed processing instruction gives the instruction back. | `Xml.Proofs.parsePI_print` |
| Reading back escaped text and escaped attribute values gives the characters back. | `Xml.Proofs.parseCharData_escapeText`, `Xml.Proofs.parseAttrValue_escapeAttr` |

A document is well formed when its names match the subset's name rule, attribute names are unique per element, text holds only legal XML characters and no two text runs stand next to each other, comment bodies contain no `--` and do not end with `-`, processing instruction targets are valid and not the reserved word `xml`, and the prolog and epilog hold only comments and processing instructions. `SPEC.md` states the rules in full. `parse_print` checks against the standard axioms only (`propext`, `Classical.choice`, `Quot.sound`), which a reader can confirm with `#print axioms Xml.Proofs.parse_print`.

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- That the parser accepts every text the subset allows, and rejects every text it forbids. The round trip does not need either, so neither is proved. The differential tests check that behaviour instead, and the results file records the outcome, including any failure.
- Anything about documents outside the subset: documents with a document type declaration, entities beyond the five predefined ones, namespaces, an XML declaration, or non-ASCII names. The parser rejects them; whether a full XML parser would accept them is not a claim here.
- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, and the check that a code is a Unicode scalar value. The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits proofs, not large data. The parser's fuel is the length of the input text, which very deep inputs can reach.

Three deliberate choices, also stated in `SPEC.md`:

- CDATA sections are a spelling, not a tree difference. CDATA content becomes ordinary character data in the same text node stream, and the printer never writes a CDATA section. The claim is at tree level, so this is sound.
- There is no line ending normalization in text, comments, processing instruction data, or CDATA: a literal carriage return reads as itself. Full XML normalizes it to a line feed. Inside attribute values both readings agree (either form reads as a space), and the printer always writes a carriage return as a character reference.
- The XML declaration is not in the model. A processing instruction target of `xml` in any letter case rejects everywhere, which keeps the declaration out.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- Python's standard library, as the oracle in the differential tests. The results file names the version used. The plan also names Go's encoding/xml and Rust's quick-xml as oracles; neither is wired in yet, and the harness says so rather than counting them.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
echo "parse 60,97,47,62" | .lake/build/bin/xml
```

That request is the text `<a/>` as character codes, and the answer is `ok:60,97,47,62`. A text the parser rejects, such as the single code `120` (the letter `x`), answers `none`. A malformed request answers `error`. See `SPEC.md` for the full protocol.

## Re-check it

Needs Linux, elan, and Python 3.11 or later.

```
lake build
grep -rn "sorry" --include="*.lean" Xml Proofs Main.lean Xml.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script rebuilds the tool if needed, runs the fixed cases, runs the differential tests against Python's `xml.etree.ElementTree` with a fixed seed, and writes the counts to `tests/TEST-RESULTS.md`.
