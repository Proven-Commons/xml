/-
  Refusal proofs: texts the parser turns away, stated for whole
  families of inputs rather than single examples.

  Each family is a text whose head is a well formed prolog printed
  in canonical form and the start of a root element, followed by
  the forbidden form and then anything at all. The proofs follow
  the parser through the prolog and the start tag with the round
  trip lemmas of `Proofs/RoundTrip.lean`, then show the step that
  turns the forbidden form away.
-/

import Xml
import Proofs.RoundTrip
import Proofs.LineEnds

namespace Xml.Proofs

open Xml

/-! ## The root element -/

/-- A text made of a printed prolog and then a less sign and a name
    start character is refused when the element reader refuses the
    root, with its line ends normalized, at every fuel large
    enough. -/
theorem parse_root_none (prolog : List Node) (hpro : MiscOk prolog)
    (c : Char) (cs0 : List Char) (hc : IsNameStart c)
    (he : ∀ f, (normEol cs0).length + 3 ≤ f →
      parseElement f ('<' :: c :: normEol cs0) = none) :
    parse (printNodes prolog ++ '<' :: c :: cs0) = none := by
  have hcr : c ≠ '\r' := fun e => not_nameChar_cr (e ▸ IsNameStart.toNameChar hc)
  have hn : normEol (printNodes prolog ++ '<' :: c :: cs0) =
      printNodes prolog ++ '<' :: c :: normEol cs0 := by
    rw [normEol_append_noCR _ _ (noCR_printNodes_misc prolog hpro),
      normEol_cons_ne (by decide), normEol_cons_ne hcr]
  show parseDocument ((normEol (printNodes prolog ++ '<' :: c :: cs0)).length + 1)
    (normEol (printNodes prolog ++ '<' :: c :: cs0)) = none
  rw [hn]
  generalize normEol cs0 = cs at he
  have hstop : ∀ f, 1 ≤ f →
      parseMisc f ('<' :: c :: cs) = some ([], skipWs ('<' :: c :: cs)) := by
    intro f hf
    cases f with
    | zero => omega
    | succ f' =>
      rw [skipWs_cons (show isWs '<' = false by decide)]
      exact parseMisc_stop hc
  have hm := parseMisc_print prolog ('<' :: c :: cs) hpro hstop
    ((printNodes prolog ++ '<' :: c :: cs).length + 1)
    (by simp only [List.length_append]; omega)
  rw [skipWs_cons (show isWs '<' = false by decide)] at hm
  have hroot := he ((printNodes prolog ++ '<' :: c :: cs).length + 1)
    (by simp only [List.length_append, List.length_cons]; omega)
  simp only [parseDocument, hm, hroot]

/-- The element reader at a start tag whose name is read whole: it
    refuses when the attribute reader refuses. -/
theorem parseElement_attrs_none {g : Nat} {name tail : List Char}
    (hn : ValidName name)
    (ht : ∀ c, tail.head? = some c → isNameChar c = false)
    (ha : parseAttrs g [] tail = none) :
    parseElement (g + 1) ('<' :: (name ++ tail)) = none := by
  simp [parseElement, parseName_append hn ht, ha]

/-- The text after a name, when it starts with the printed
    attributes and then more text, does not start with a name
    character, as long as the more text does not. -/
theorem printAttrs_head_not_name (attrs : List (List Char × List Char))
    (tail : List Char)
    (ht : ∀ c, tail.head? = some c → isNameChar c = false) :
    ∀ c, (printAttrs attrs ++ tail).head? = some c → isNameChar c = false := by
  intro c hc
  cases attrs with
  | nil => exact ht c (by simpa [printAttrs] using hc)
  | cons kv as =>
    simp only [printAttrs, List.cons_append, List.head?_cons] at hc
    rw [← Option.some.inj hc]
    exact isNameChar_false_of not_nameChar_space

/-- A root start tag with printed attributes, at the head of a text
    after a printed prolog, is refused when the attribute reader
    refuses whatever follows the printed attributes, with its line
    ends normalized, at any fuel from one up. -/
theorem parse_attrs_none (prolog : List Node) (hpro : MiscOk prolog)
    (name : List Char) (hname : ValidName name)
    (attrs : List (List Char × List Char)) (hattrs : AttrsOk attrs)
    (tail0 : List Char)
    (ht : ∀ c, (printAttrs attrs ++ normEol tail0).head? = some c →
      isNameChar c = false)
    (hcont : ∀ f, 1 ≤ f → parseAttrs f attrs (normEol tail0) = none) :
    parse (printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++ tail0))) =
      none := by
  have hnn := noCR_validName hname
  obtain ⟨c0, ds, hq, hc0, hds⟩ := hname
  subst hq
  rw [List.cons_append]
  apply parse_root_none prolog hpro c0 _ hc0
  have hds' : '\r' ∉ ds := fun m => hnn (List.mem_cons_of_mem _ m)
  rw [normEol_append_noCR _ _ hds',
    normEol_append_noCR _ _ (noCR_printAttrs attrs hattrs)]
  generalize normEol tail0 = tail at ht hcont
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    have hlen : ds.length + (printAttrs attrs).length + tail.length + 2 ≤ g := by
      have h := hf
      simp only [List.length_append] at h
      omega
    have hpa := printAttrs_length_ge attrs
    have hpv := printAttrs_length_ge_value attrs
    have ha : parseAttrs g [] (printAttrs attrs ++ tail) = none := by
      apply parseAttrs_print attrs [] tail g none hattrs
        (by intro kv _ e; simp at e)
      · intro kv hkv
        have h1 := hpv kv hkv
        omega
      · omega
      · intro f' hf'
        simpa using hcont f' hf'
    exact parseElement_attrs_none (name := c0 :: ds) ⟨c0, ds, rfl, hc0, hds⟩
      ht ha

/-! ## The name `xmlns` -/

theorem validName_xmlns : ValidName xmlnsName :=
  ⟨'x', ['m', 'l', 'n', 's'], rfl, isNameStart_iff.mp (by decide),
    by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      exact isNameChar_iff.mp (by decide)⟩

/-- The attribute reader refuses an attribute named `xmlns`, read
    whole, whatever comes after the name. -/
theorem parseAttrs_xmlns (f : Nat) (hf : 1 ≤ f)
    (acc : List (List Char × List Char)) (rest : List Char)
    (hr : ∀ c, rest.head? = some c → isNameChar c = false) :
    parseAttrs f acc (' ' :: (xmlnsName ++ rest)) = none := by
  cases f with
  | zero => omega
  | succ g =>
    have hsk : skipWs (' ' :: (xmlnsName ++ rest)) =
        'x' :: 'm' :: 'l' :: 'n' :: 's' :: rest := by
      simp [skipWs, isWs, xmlnsName]
    have hpn : parseName ('x' :: 'm' :: 'l' :: 'n' :: 's' :: rest) =
        some (xmlnsName, rest) :=
      parseName_append validName_xmlns hr
    rw [parseAttrs, hsk, hpn]
    rfl

/-- An attribute named `xmlns` on the root element is refused,
    after any well formed prolog and any well formed attributes
    before it, whatever follows the name. -/
theorem rejects_xmlns (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs)
    (hrest : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      ' ' :: xmlnsName ++ rest) = none := by
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      ' ' :: xmlnsName ++ rest =
      printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++
        ' ' :: (xmlnsName ++ rest))) := by
    simp [List.append_assoc]
  rw [e]
  have hn : normEol (' ' :: (xmlnsName ++ rest)) =
      ' ' :: (xmlnsName ++ normEol rest) := by
    rw [normEol_cons_ne (by decide),
      normEol_append_noCR _ _ (by decide)]
  apply parse_attrs_none prolog hpro name hname attrs hattrs
  · rw [hn]
    apply printAttrs_head_not_name
    intro c hc
    simp at hc
    rw [← hc]
    exact isNameChar_false_of not_nameChar_space
  · intro f hf
    rw [hn]
    exact parseAttrs_xmlns f hf attrs (normEol rest)
      (normEol_head_not_name rest hrest)

/-! ## Whitespace between attributes -/

/-- The printed attributes, when there is at least one, start with
    a space, which is not a name character. -/
theorem printAttrs_head_space (attrs : List (List Char × List Char))
    (hne : attrs ≠ []) (tail : List Char) :
    ∀ c, (printAttrs attrs ++ tail).head? = some c →
      isNameChar c = false := by
  intro c hc
  cases attrs with
  | nil => exact absurd rfl hne
  | cons kv as =>
    simp only [printAttrs, List.cons_append, List.head?_cons] at hc
    rw [← Option.some.inj hc]
    exact isNameChar_false_of not_nameChar_space

/-- The attribute reader refuses a name that starts right where
    the text does, with no whitespace before it. -/
theorem parseAttrs_no_space (f : Nat) (hf : 1 ≤ f)
    (acc : List (List Char × List Char)) (c : Char) (rest : List Char)
    (hc : IsNameStart c) :
    parseAttrs f acc (c :: rest) = none := by
  cases f with
  | zero => omega
  | succ g =>
    have hw : isWs c = false := isWs_false_of_not (IsNameStart.ne_ws hc)
    have h1 : c ≠ '/' := IsNameStart.ne_slash hc
    have h2 : c ≠ '>' := IsNameStart.ne_of_test hc (by decide)
    simp only [parseAttrs, skipWs, hw, startsWithWs, Bool.and_false,
      Bool.false_eq_true, ite_false]
    split
    · rename_i r e
      exact absurd (List.cons.inj e).1 h1
    · rename_i r e
      exact absurd (List.cons.inj e).1 h2
    · rfl
    · rfl

/-- An attribute name that starts right after the closing quote of
    the attribute before it, with no whitespace between them, is
    refused, on the root element after any well formed prolog and
    at least one well formed attribute, printed, whatever follows
    the first character of the name. -/
theorem rejects_attribute_without_space (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (c : Char) (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name)
    (hattrs : AttrsOk attrs) (hne : attrs ≠ []) (hc : IsNameStart c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      c :: rest) = none := by
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      c :: rest =
      printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++
        c :: rest)) := by
    simp [List.append_assoc]
  rw [e]
  have hcr : c ≠ '\r' := fun e => not_nameChar_cr (e ▸ IsNameStart.toNameChar hc)
  apply parse_attrs_none prolog hpro name hname attrs hattrs (c :: rest)
    (printAttrs_head_space attrs hne _)
  intro f hf
  rw [normEol_cons_ne hcr]
  exact parseAttrs_no_space f hf attrs c (normEol rest) hc

end Xml.Proofs
