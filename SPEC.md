# Specification: xml

A parser and printer in Lean for a safe subset of XML 1.0 (Fifth
Edition), narrowed as stated here. A reviewer who did not write
this specification approves it, together with the statement file
`Spec.lean`. No reviewer has approved them yet, so nothing here
counts toward the verified bar yet.

Text is `List Char`. A Lean `Char` is one Unicode scalar value.

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
- Whitespace may appear between attributes, around the equals
  sign, and before the closing bracket of a start tag or an end
  tag.
- In an attribute value: character references and the five
  predefined entities are expanded on read. A raw `<` rejects.
  A raw `&` that does not begin a valid reference rejects.
- Attribute value normalization: a literal tab or line feed in
  a value reads as one space, and a literal carriage return or
  carriage return with line feed reads as one space. This is
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
  kind in this subset, so the parser never expands an entity
  beyond the five predefined ones, because none exist.

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
  and do not end with `-`;
- processing instruction targets are valid names and not the
  reserved word, their data holds only legal characters, never
  contains `?>`, and never starts with whitespace;
- the root is an element, and the prolog and epilog hold only
  comments and processing instructions.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The refusal
theorems are single inputs; the tests in `tests/` cover
each rule on many more inputs.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed document gives the document back | `Spec.parse_print` |
| A document carrying a document type declaration is refused | `Spec.rejects_doctype` |
| A reference to an entity the subset does not define is refused | `Spec.rejects_undefined_entity` |
| An end tag that does not match the start tag is refused | `Spec.rejects_mismatched_tags` |
| An element with no end tag is refused | `Spec.rejects_unclosed_element` |
| A second root element is refused | `Spec.rejects_second_root` |
| Character data before the root element is refused | `Spec.rejects_text_before_root` |
| An attribute name standing twice on one element is refused | `Spec.rejects_duplicate_attribute` |
| A raw less sign inside an attribute value is refused | `Spec.rejects_lt_in_attribute` |
| The run `]]>` inside text is refused | `Spec.rejects_cdata_close_in_text` |
| Two dashes in a row inside a comment body are refused | `Spec.rejects_dashdash_in_comment` |
| A character reference naming a surrogate value is refused | `Spec.rejects_surrogate_ref` |
| A character reference naming zero is refused | `Spec.rejects_zero_ref` |
| A colon in a name is refused | `Spec.rejects_colon_in_name` |
| A name starting with a digit is refused | `Spec.rejects_digit_name` |
| An attribute value with no quotes is refused | `Spec.rejects_unquoted_attribute` |
| A CDATA section in the prolog is refused | `Spec.rejects_cdata_in_prolog` |
| The XML declaration form is refused | `Spec.rejects_xml_declaration` |
| An attribute named `xmlns` on the root element is refused, after any well formed prolog and any well formed attributes before it, printed, whatever follows the name that does not make it longer | `Spec.rejects_xmlns` |

The round trip behind `Spec.parse_print` is
`Xml.Proofs.parse_print` in `Proofs/RoundTrip.lean`. Its
proofs rest on helper round trips proved in the same file:
one element and a list of content nodes together
(`Xml.Proofs.elem_nodes`), a prolog or epilog list
(`Xml.Proofs.parseMisc_print`), a printed comment body
(`Xml.Proofs.parseCommentBody_print`), a printed
processing instruction (`Xml.Proofs.parsePI_print`), and
escaped text and attribute values read back
(`Xml.Proofs.parseCharData_escapeText`,
`Xml.Proofs.parseAttrValue_escapeAttr`). Each proof in
`Proofs/SpecProofs.lean` uses no axiom but the three
standard ones (`propext`, `Classical.choice`,
`Quot.sound`): `comparator.json` names those three as the
permitted axioms, and `lake comparator` checks the proofs
against that list.

## Boundaries and named differences

- No line ending normalization in text, comments, processing
  instruction data, or CDATA sections: a literal carriage
  return there reads as itself. Full XML normalizes carriage
  return and carriage return with line feed to a line feed
  before parsing, and Python's ElementTree does so. That is a
  difference between this subset and full XML, stated plainly:
  a text a full XML parser reads one way can read with a line
  feed where this parser keeps a carriage return. Inside
  attribute values both readings agree, because normalization
  there sends either form to a space, and in printed form a
  carriage return is always a character reference.
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
