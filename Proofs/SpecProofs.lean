/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The round trip is the theorem proved in
  `Proofs/RoundTrip.lean`. The refusals are single inputs,
  checked in the kernel with `decide +kernel`: no native
  evaluation, which the bar forbids.
-/

import Xml
import Proofs.RoundTrip
import Proofs.Refusals
import Proofs.LineEnds

open Xml

theorem Spec.parse_print (d : Document) (hwf : WF d) :
    parse (print d) = some d :=
  Xml.Proofs.parse_print d hwf


theorem Spec.rejects_doctype :
    (parse "<!DOCTYPE a><a/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_undefined_entity :
    (parse "<a>&nbsp;</a>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_mismatched_tags :
    (parse "<a></b>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_unclosed_element :
    (parse "<a>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_second_root :
    (parse "<a/><b/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_text_before_root :
    (parse "x<a/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_duplicate_attribute :
    (parse "<a b=\"1\" b=\"2\"/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_lt_in_attribute :
    (parse "<a b=\"x<y\"/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_cdata_close_in_text :
    (parse "<a>x]]>y</a>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_dashdash_in_comment :
    (parse "<a><!-- x -- y --></a>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_surrogate_ref :
    (parse "<a>&#xD800;</a>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_zero_ref :
    (parse "<a>&#0;</a>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_colon_in_name :
    (parse "<a:b/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_digit_name :
    (parse "<1a/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_unquoted_attribute :
    (parse "<a b=x/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_cdata_in_prolog :
    (parse "<![CDATA[x]]><a/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_xml_declaration :
    (parse "<?xml version=\"1.0\"?><a/>".toList).isSome = false := by
  decide +kernel


theorem Spec.rejects_xmlns (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs)
    (hrest : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      ' ' :: xmlnsName ++ rest) = none :=
  Xml.Proofs.rejects_xmlns prolog name attrs rest hpro hname hattrs hrest


theorem Spec.rejects_attribute_without_space (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (c : Char) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs) (hne : attrs ≠ []) (hc : IsNameStart c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      c :: rest) = none :=
  Xml.Proofs.rejects_attribute_without_space prolog name attrs c rest
    hpro hname hattrs hne hc


theorem Spec.crlf_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') :
    parse (pre ++ '\r' :: '\n' :: post) = parse (pre ++ '\n' :: post) :=
  Xml.Proofs.crlf_reads_as_lf pre post hpre


theorem Spec.cr_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') (hpost : post.head? ≠ some '\n') :
    parse (pre ++ '\r' :: post) = parse (pre ++ '\n' :: post) :=
  Xml.Proofs.cr_reads_as_lf pre post hpre hpost
