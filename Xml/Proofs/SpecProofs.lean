/-
  Proofs of the statements in `Xml/Spec.lean`, under the same names.

  Each proof is the theorem of the same shape in the proof files:
  the round trip in `Xml/Proofs/RoundTrip.lean`, well formedness of
  every accepted document in `Xml/Proofs/ParseWF.lean`, line ends in
  `Xml/Proofs/LineEnds.lean`, and the refused families in
  `Xml/Proofs/Refusals.lean`. No native evaluation, which the bar
  forbids.
-/

import Xml
import Xml.Proofs.RoundTrip
import Xml.Proofs.Refusals
import Xml.Proofs.LineEnds
import Xml.Proofs.ParseWF

open Xml


theorem Xml.Spec.parse_print (d : Document) (hwf : WF d) :
    parse (print d) = some d :=
  Xml.Proofs.parse_print d hwf

theorem Xml.Spec.parse_wf (cs : List Char) (d : Document)
    (h : parse cs = some d) : WF d :=
  Xml.Proofs.parse_wf cs d h

theorem Xml.Spec.print_parse (cs : List Char) (d : Document)
    (h : parse cs = some d) : parse (print d) = some d :=
  Xml.Proofs.print_parse cs d h

theorem Xml.Spec.crlf_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') :
    parse (pre ++ '\r' :: '\n' :: post) = parse (pre ++ '\n' :: post) :=
  Xml.Proofs.crlf_reads_as_lf pre post hpre

theorem Xml.Spec.cr_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') (hpost : post.head? ≠ some '\n') :
    parse (pre ++ '\r' :: post) = parse (pre ++ '\n' :: post) :=
  Xml.Proofs.cr_reads_as_lf pre post hpre hpost

theorem Xml.Spec.rejects_doctype (prolog : List Node) (rest : List Char)
    (hpro : MiscOk prolog) :
    parse (printNodes prolog ++ ['<', '!', 'D', 'O', 'C', 'T', 'Y', 'P', 'E'] ++
      rest) = none :=
  Xml.Proofs.rejects_doctype prolog rest hpro

theorem Xml.Spec.rejects_cdata_in_prolog (prolog : List Node) (rest : List Char)
    (hpro : MiscOk prolog) :
    parse (printNodes prolog ++ ['<', '!', '[', 'C', 'D', 'A', 'T', 'A', '['] ++
      rest) = none :=
  Xml.Proofs.rejects_cdata_in_prolog prolog rest hpro

theorem Xml.Spec.rejects_xml_declaration (t rest : List Char) (ht : ValidName t)
    (hx : IsXmlTarget t) (hr : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse ('<' :: '?' :: t ++ rest) = none :=
  Xml.Proofs.rejects_xml_declaration t rest ht hx hr

theorem Xml.Spec.rejects_text_before_root (prolog : List Node) (c : Char)
    (rest : List Char) (hpro : MiscOk prolog) (hws : ¬ IsWs c)
    (hlt : c ≠ '<') : parse (printNodes prolog ++ c :: rest) = none :=
  Xml.Proofs.rejects_text_before_root prolog c rest hpro hws hlt

theorem Xml.Spec.rejects_second_root (d : Document) (c : Char) (rest : List Char)
    (hwf : WF d) (hc : IsNameStart c) :
    parse (print d ++ '<' :: c :: rest) = none :=
  Xml.Proofs.rejects_second_root d c rest hwf hc

theorem Xml.Spec.rejects_digit_name (prolog : List Node) (d : Char)
    (rest : List Char) (hpro : MiscOk prolog)
    (hd : d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) :
    parse (printNodes prolog ++ '<' :: d :: rest) = none :=
  Xml.Proofs.rejects_digit_name prolog d rest hpro hd

theorem Xml.Spec.rejects_colon_in_name (prolog : List Node) (name rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) :
    parse (printNodes prolog ++ '<' :: name ++ ':' :: rest) = none :=
  Xml.Proofs.rejects_colon_in_name prolog name rest hpro hname

theorem Xml.Spec.rejects_mismatched_tags (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (content : List Node)
    (other rest : List Char)
    (hpro : MiscOk prolog) (hel : WFNode (.elem name attrs content))
    (hother : ValidName other) (hne : other ≠ name) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
      printNodes content ++ '<' :: '/' :: other ++ '>' :: rest) = none :=
  Xml.Proofs.rejects_mismatched_tags prolog name attrs content other rest hpro hel hother hne

theorem Xml.Spec.rejects_unclosed_element (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char))
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ['>']) =
      none :=
  Xml.Proofs.rejects_unclosed_element prolog name attrs hpro hname hattrs


theorem Xml.Spec.rejects_undefined_entity (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre e post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) (he : ValidName e)
    (hfive : e ∉ [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
      ['q', 'u', 'o', 't']]) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      '&' :: e ++ ';' :: post) = none :=
  Xml.Proofs.rejects_undefined_entity prolog name attrs pre e post hpro hname hattrs hlt hamp he hfive

theorem Xml.Spec.rejects_undefined_entity_in_attribute (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (a pre e post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hq : '"' ∉ pre) (hamp : '&' ∉ pre) (he : ValidName e)
    (hfive : e ∉ [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
      ['q', 'u', 'o', 't']]) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '&' :: e ++ ';' :: post) = none :=
  Xml.Proofs.rejects_undefined_entity_in_attribute prolog name attrs a pre e post hpro hname hattrs ha hq hamp he hfive

theorem Xml.Spec.rejects_surrogate_ref (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      ['&', '#', 'x', 'D', '8', '0', '0', ';'] ++ post) = none :=
  Xml.Proofs.rejects_surrogate_ref prolog name attrs pre post hpro hname hattrs hlt hamp

theorem Xml.Spec.rejects_zero_ref (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      ['&', '#', '0', ';'] ++ post) = none :=
  Xml.Proofs.rejects_zero_ref prolog name attrs pre post hpro hname hattrs hlt hamp

theorem Xml.Spec.rejects_cdata_close_in_text (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      [']', ']', '>'] ++ post) = none :=
  Xml.Proofs.rejects_cdata_close_in_text prolog name attrs pre post hpro hname hattrs hlt hamp

theorem Xml.Spec.rejects_dashdash_in_comment (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (body : List Char) (c : Char)
    (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hbody : WFNode (.comment body)) (hc : c ≠ '>') :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
      '<' :: '!' :: '-' :: '-' :: body ++ '-' :: '-' :: c :: rest) = none :=
  Xml.Proofs.rejects_dashdash_in_comment prolog name attrs body c rest hpro hname hattrs hbody hc

theorem Xml.Spec.rejects_duplicate_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a v rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hdup : ∃ w, (a, w) ∈ attrs) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      printAttrs [(a, v)] ++ rest) = none :=
  Xml.Proofs.rejects_duplicate_attribute prolog name attrs a v rest hpro hname hattrs hdup

theorem Xml.Spec.rejects_lt_in_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a pre rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hq : '"' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '<' :: rest) = none :=
  Xml.Proofs.rejects_lt_in_attribute prolog name attrs a pre rest hpro hname hattrs ha hq hamp

theorem Xml.Spec.rejects_unquoted_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a : List Char) (c : Char)
    (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hc1 : c ≠ '"') (hc2 : c ≠ '\'') (hcw : ¬ IsWs c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: c :: rest) = none :=
  Xml.Proofs.rejects_unquoted_attribute prolog name attrs a c rest hpro hname hattrs ha hc1 hc2 hcw

theorem Xml.Spec.rejects_attribute_without_space (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (c : Char) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs) (hne : attrs ≠ []) (hc : IsNameStart c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      c :: rest) = none :=
  Xml.Proofs.rejects_attribute_without_space prolog name attrs c rest hpro hname hattrs hne hc

theorem Xml.Spec.rejects_xmlns (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs)
    (hrest : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      ' ' :: xmlnsName ++ rest) = none :=
  Xml.Proofs.rejects_xmlns prolog name attrs rest hpro hname hattrs hrest
