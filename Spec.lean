/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `Xml/Value.lean` and
  `Xml/Parse.lean`, the code under proof named in `bar.toml`. No
  definition of their own is needed, so this project has no
  `Spec/Defs.lean`.
-/

import Xml

open Xml

/-! ## The round trip

The statement the slice stands on. It is the statement of the
proved theorem of the same shape in `Proofs/RoundTrip.lean`, over
the same well formedness predicate, `Xml.WF`. -/

/-- Parsing the printed form of a well formed document gives the
    document back. So a printer that wrote nothing, or wrote
    something shorter, fails this statement. -/
theorem Spec.parse_print (d : Document) (hwf : WF d) :
    parse (print d) = some d := sorry

/-! ## Every accepted document

The two statements below hold for every text. A parser that refuses
every text meets both, so they are paired with `Spec.parse_print`,
which such a parser fails. -/

/-- Every text the parser accepts gives a well formed document, as
    `Xml.WF` defines it: every name follows the subset's name rule
    (so no name holds a colon or starts with a digit), no attribute
    name stands twice on an element and none is `xmlns`, every
    character in text, attribute values, comments and processing
    instruction data is a legal XML character, no two text runs
    stand next to each other and none is empty, comment bodies hold
    no `--`, do not end with `-` and hold no carriage return,
    processing instruction targets are not `xml` in any letter case
    and their data holds no `?>`, does not start with whitespace and
    holds no carriage return, the root is an element, and the prolog
    and epilog hold only comments and processing instructions. -/
theorem Spec.parse_wf (cs : List Char) (d : Document)
    (h : parse cs = some d) : WF d := sorry

/-- The plan's main claim, as written: printing a parsed document
    gives a text that parses to the same document. -/
theorem Spec.print_parse (cs : List Char) (d : Document)
    (h : parse cs = some d) : parse (print d) = some d := sorry

/-! ## Line ends -/

/-- Line ends are normalized as XML 1.0 section 2.11 requires: a
    carriage return followed by a line feed reads exactly as one
    line feed, wherever it stands in the text, unless the text
    before it ends with a carriage return (which pairs with the
    line feed first). -/
theorem Spec.crlf_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') :
    parse (pre ++ '\r' :: '\n' :: post) = parse (pre ++ '\n' :: post) :=
  sorry

/-- A carriage return that is not followed by a line feed reads
    exactly as a line feed, wherever it stands in the text, unless
    the text before it ends with a carriage return. -/
theorem Spec.cr_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') (hpost : post.head? ≠ some '\n') :
    parse (pre ++ '\r' :: post) = parse (pre ++ '\n' :: post) := sorry

/-! ## Refused texts

Each statement below is about a family of texts, not one input. The
families share a shape: a text that starts with a well formed
prolog (`MiscOk`), printed in canonical form, then, for most of
them, the root's start tag with a valid name and well formed
attributes (`AttrsOk`), also printed, then the form the rule turns
away, then anything at all. Each docstring says which part is
fixed. None says that the form is refused in every position: a
statement about the root's first text run says nothing about a
nested element. `SPEC.md` and `README.md` list what is left
out. -/

/-- A document type declaration right after the prolog is refused,
    whatever follows `<!DOCTYPE`. -/
theorem Spec.rejects_doctype (prolog : List Node) (rest : List Char)
    (hpro : MiscOk prolog) :
    parse (printNodes prolog ++ ['<', '!', 'D', 'O', 'C', 'T', 'Y', 'P', 'E'] ++
      rest) = none := sorry

/-- A CDATA section right after the prolog is refused, whatever
    follows `<![CDATA[`: CDATA stands in element content only. -/
theorem Spec.rejects_cdata_in_prolog (prolog : List Node) (rest : List Char)
    (hpro : MiscOk prolog) :
    parse (printNodes prolog ++ ['<', '!', '[', 'C', 'D', 'A', 'T', 'A', '['] ++
      rest) = none := sorry

/-- The XML declaration is refused: a text that starts with `<?` and
    a processing instruction target that is the word `xml` in any
    letter case, whatever follows the target that does not make it
    longer. -/
theorem Spec.rejects_xml_declaration (t rest : List Char) (ht : ValidName t)
    (hx : IsXmlTarget t) (hr : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse ('<' :: '?' :: t ++ rest) = none := sorry

/-- Character data before the root is refused: right after the
    prolog, any character that is neither whitespace nor a less
    sign, whatever follows. -/
theorem Spec.rejects_text_before_root (prolog : List Node) (c : Char)
    (rest : List Char) (hpro : MiscOk prolog) (hws : ¬ IsWs c)
    (hlt : c ≠ '<') : parse (printNodes prolog ++ c :: rest) = none := sorry

/-- A second root is refused: any well formed document, printed,
    followed by a less sign and a name start character, then
    anything. -/
theorem Spec.rejects_second_root (d : Document) (c : Char) (rest : List Char)
    (hwf : WF d) (hc : IsNameStart c) :
    parse (print d ++ '<' :: c :: rest) = none := sorry

/-- An element name that starts with a digit is refused: right
    after the prolog, a less sign and any of the ten digits,
    whatever follows. -/
theorem Spec.rejects_digit_name (prolog : List Node) (d : Char)
    (rest : List Char) (hpro : MiscOk prolog)
    (hd : d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) :
    parse (printNodes prolog ++ '<' :: d :: rest) = none := sorry

/-- A colon in an element name is refused: right after the prolog,
    a less sign, any valid name, then a colon, whatever follows. In
    XML a colon signals namespace use, and namespaces are out. -/
theorem Spec.rejects_colon_in_name (prolog : List Node) (name rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) :
    parse (printNodes prolog ++ '<' :: name ++ ':' :: rest) = none := sorry

/-- An end tag that names a different element is refused: right
    after the prolog, any well formed root element printed in full,
    except that its end tag names another valid name, then
    anything. -/
theorem Spec.rejects_mismatched_tags (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (content : List Node)
    (other rest : List Char)
    (hpro : MiscOk prolog) (hel : WFNode (.elem name attrs content))
    (hother : ValidName other) (hne : other ≠ name) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
      printNodes content ++ '<' :: '/' :: other ++ '>' :: rest) = none := sorry

/-- An element with no end tag is refused: right after the prolog,
    the root's start tag with any valid name and well formed
    attributes, printed, at the very end of the text. -/
theorem Spec.rejects_unclosed_element (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char))
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ['>']) =
      none := sorry

/-- A reference to an entity other than the five predefined ones is
    refused, in the root's first run of character data: after the
    prolog and the root's start tag, any text with no less sign and
    no ampersand, then `&`, any valid name other than `lt`, `gt`,
    `amp`, `apos` and `quot`, and `;`, whatever follows. No such
    entity is expanded there. -/
theorem Spec.rejects_undefined_entity (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre e post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) (he : ValidName e)
    (hfive : e ∉ [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
      ['q', 'u', 'o', 't']]) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      '&' :: e ++ ';' :: post) = none := sorry

/-- The same in an attribute value: after the prolog and the root's
    start tag with its well formed attributes, a space, any valid
    attribute name, `="`, any text with no double quote and no
    ampersand, then `&`, a valid name other than the five, and `;`,
    whatever follows. -/
theorem Spec.rejects_undefined_entity_in_attribute (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (a pre e post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hq : '"' ∉ pre) (hamp : '&' ∉ pre) (he : ValidName e)
    (hfive : e ∉ [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
      ['q', 'u', 'o', 't']]) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '&' :: e ++ ';' :: post) = none := sorry

/-- The character reference `&#xD800;`, a surrogate, is refused in
    the root's first run of character data: after the prolog and
    the root's start tag, any text with no less sign and no
    ampersand, then `&#xD800;`, whatever follows. -/
theorem Spec.rejects_surrogate_ref (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      ['&', '#', 'x', 'D', '8', '0', '0', ';'] ++ post) = none := sorry

/-- The character reference `&#0;` is refused in the same place. -/
theorem Spec.rejects_zero_ref (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      ['&', '#', '0', ';'] ++ post) = none := sorry

/-- The run `]]>` is refused in the root's first run of character
    data: after the prolog and the root's start tag, any text with
    no less sign and no ampersand, then `]]>`, whatever follows. -/
theorem Spec.rejects_cdata_close_in_text (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      [']', ']', '>'] ++ post) = none := sorry

/-- Two dashes inside a comment are refused, for a comment that is
    the root's first content: after the prolog and the root's start
    tag, `<!--`, a body a well formed comment may hold, `--`, then
    any character but `>`, whatever follows. -/
theorem Spec.rejects_dashdash_in_comment (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (body : List Char) (c : Char)
    (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hbody : WFNode (.comment body)) (hc : c ≠ '>') :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
      '<' :: '!' :: '-' :: '-' :: body ++ '-' :: '-' :: c :: rest) = none := sorry

/-- A repeated attribute name is refused on the root: after the
    prolog and the root's start tag with its well formed attributes,
    one more attribute, printed, whose name is already among them,
    with any value, whatever follows. -/
theorem Spec.rejects_duplicate_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a v rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hdup : ∃ w, (a, w) ∈ attrs) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      printAttrs [(a, v)] ++ rest) = none := sorry

/-- A raw less sign in an attribute value is refused on the root:
    after the prolog and the root's start tag with its well formed
    attributes, a space, any valid attribute name, `="`, any text
    with no double quote and no ampersand, then `<`, whatever
    follows. -/
theorem Spec.rejects_lt_in_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a pre rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hq : '"' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '<' :: rest) = none := sorry

/-- An attribute value with no quotes is refused on the root: after
    the prolog and the root's start tag with its well formed
    attributes, a space, any valid attribute name, `=`, then any
    character that is no quote and no whitespace, whatever
    follows. -/
theorem Spec.rejects_unquoted_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a : List Char) (c : Char)
    (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hc1 : c ≠ '"') (hc2 : c ≠ '\'') (hcw : ¬ IsWs c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: c :: rest) = none := sorry

/-- An attribute must have whitespace before it, as XML 1.0
    productions [40] and [44] require: on the root, after the prolog
    and at least one well formed attribute, printed, a name start
    character right after the closing quote is refused, whatever
    follows. -/
theorem Spec.rejects_attribute_without_space (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (c : Char) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs) (hne : attrs ≠ []) (hc : IsNameStart c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      c :: rest) = none := sorry

/-- An attribute named `xmlns`, the default namespace declaration,
    is refused on the root: namespaces are out of this subset, and
    the colon ban on names does not reach this name. After the
    prolog and the root's start tag with any well formed attributes,
    printed, a space and `xmlns`, whatever follows the name that
    does not make it longer. -/
theorem Spec.rejects_xmlns (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs)
    (hrest : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      ' ' :: xmlnsName ++ rest) = none := sorry
