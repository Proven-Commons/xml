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

/-! ## Refused inputs

Single inputs the parser refuses, one for each headline rule of
`SPEC.md`. Each input is one of the named rejection cases in the
test harness. The differential tests cover these rules on many
more inputs; these statements pin them so a reader of the
specification can check each rule against one concrete case. -/

/-- A document carrying a document type declaration is refused,
    not read leniently. -/
theorem Spec.rejects_doctype :
    (parse "<!DOCTYPE a><a/>".toList).isSome = false := sorry

/-- A reference to an entity the subset does not define is
    refused: no entity is ever expanded, because none exist. -/
theorem Spec.rejects_undefined_entity :
    (parse "<a>&nbsp;</a>".toList).isSome = false := sorry

/-- An end tag that does not match the start tag is refused. -/
theorem Spec.rejects_mismatched_tags :
    (parse "<a></b>".toList).isSome = false := sorry

/-- An element with no end tag is refused. -/
theorem Spec.rejects_unclosed_element :
    (parse "<a>".toList).isSome = false := sorry

/-- A document has one root element; a second one is refused. -/
theorem Spec.rejects_second_root :
    (parse "<a/><b/>".toList).isSome = false := sorry

/-- Character data before the root element is refused. -/
theorem Spec.rejects_text_before_root :
    (parse "x<a/>".toList).isSome = false := sorry

/-- An attribute name standing twice on one element is refused. -/
theorem Spec.rejects_duplicate_attribute :
    (parse "<a b=\"1\" b=\"2\"/>".toList).isSome = false := sorry

/-- A raw less sign inside an attribute value is refused. -/
theorem Spec.rejects_lt_in_attribute :
    (parse "<a b=\"x<y\"/>".toList).isSome = false := sorry

/-- The run `]]>` inside text is refused, as XML requires
    outside a CDATA section. -/
theorem Spec.rejects_cdata_close_in_text :
    (parse "<a>x]]>y</a>".toList).isSome = false := sorry

/-- Two dashes in a row inside a comment body are refused. -/
theorem Spec.rejects_dashdash_in_comment :
    (parse "<a><!-- x -- y --></a>".toList).isSome = false := sorry

/-- A character reference naming a surrogate value is refused:
    a surrogate is not a legal XML character. -/
theorem Spec.rejects_surrogate_ref :
    (parse "<a>&#xD800;</a>".toList).isSome = false := sorry

/-- A character reference naming zero is refused: zero is not a
    legal XML character. -/
theorem Spec.rejects_zero_ref :
    (parse "<a>&#0;</a>".toList).isSome = false := sorry

/-- A colon in a name is refused: in XML a colon signals
    namespace use, and namespaces are out of this subset. -/
theorem Spec.rejects_colon_in_name :
    (parse "<a:b/>".toList).isSome = false := sorry

/-- A name starting with a digit is refused. -/
theorem Spec.rejects_digit_name :
    (parse "<1a/>".toList).isSome = false := sorry

/-- An attribute value with no quotes is refused. -/
theorem Spec.rejects_unquoted_attribute :
    (parse "<a b=x/>".toList).isSome = false := sorry

/-- A CDATA section in the prolog is refused: CDATA stands in
    element content only. -/
theorem Spec.rejects_cdata_in_prolog :
    (parse "<![CDATA[x]]><a/>".toList).isSome = false := sorry

/-- The XML declaration form is refused: the declaration is not
    part of this subset, and a target of `xml` rejects
    everywhere. -/
theorem Spec.rejects_xml_declaration :
    (parse "<?xml version=\"1.0\"?><a/>".toList).isSome = false := sorry
