/-
  Refusal proofs: texts the parser turns away, stated for whole
  families of inputs rather than single examples.

  Each family is a text whose head is a well formed prolog printed
  in canonical form and the start of a root element, followed by
  the forbidden form and then anything at all. The proofs follow
  the parser through the prolog and the start tag with the round
  trip lemmas of `Xml/Proofs/RoundTrip.lean`, then show the step that
  turns the forbidden form away.
-/

import Xml
import Xml.Proofs.RoundTrip
import Xml.Proofs.LineEnds
import Xml.Proofs.ParseWF

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

/-! ## Toolkit: after the prolog -/

/-- A text made of a printed prolog and then a part where the prolog
    reader stops and the element reader refuses, with its line ends
    normalized, is refused. -/
theorem parse_prolog_none (prolog : List Node) (hpro : MiscOk prolog)
    (X0 : List Char)
    (hstop : ∀ f, 1 ≤ f →
      parseMisc f (normEol X0) = some ([], skipWs (normEol X0)))
    (he : ∀ f, 1 ≤ f → parseElement f (skipWs (normEol X0)) = none) :
    parse (printNodes prolog ++ X0) = none := by
  have hn : normEol (printNodes prolog ++ X0) = printNodes prolog ++ normEol X0 :=
    normEol_append_noCR _ _ (noCR_printNodes_misc prolog hpro)
  show parseDocument ((normEol (printNodes prolog ++ X0)).length + 1)
    (normEol (printNodes prolog ++ X0)) = none
  rw [hn]
  generalize normEol X0 = X at hstop he
  have hm := parseMisc_print prolog X hpro hstop
    ((printNodes prolog ++ X).length + 1)
    (by simp only [List.length_append]; omega)
  have hroot := he ((printNodes prolog ++ X).length + 1) (by omega)
  simp only [parseDocument, hm, hroot]

/-- The prolog reader stops at a less sign followed by a character
    that is neither the bang of a comment nor a question mark. -/
theorem parseMisc_stop_lt {f : Nat} {c : Char} {cs : List Char}
    (h1 : c ≠ '!') (h2 : c ≠ '?') :
    parseMisc (f + 1) ('<' :: c :: cs) = some ([], '<' :: c :: cs) := by
  have h3 : skipWs ('<' :: c :: cs) = '<' :: c :: cs :=
    skipWs_cons (by decide)
  simp [parseMisc, h3, h1, h2]

/-- The prolog reader stops at a less sign, a character that is not
    a question mark, and a character that is not a dash. The two
    characters are variables here: the nanoda kernel recurses past
    its stack when it has to compare a character literal with a
    different literal pattern while checking a matcher, so the
    literal case below instantiates this one. -/
theorem parseMisc_stop_two {f : Nat} {b c : Char} {cs : List Char}
    (hb : b ≠ '?') (hc : c ≠ '-') :
    parseMisc (f + 1) ('<' :: b :: c :: cs) =
      some ([], '<' :: b :: c :: cs) := by
  have h3 : skipWs ('<' :: b :: c :: cs) = '<' :: b :: c :: cs :=
    skipWs_cons (by decide)
  simp [parseMisc, h3, hb, hc]

/-- The prolog reader stops at `<!` followed by a character that is
    not a dash. -/
theorem parseMisc_stop_bang {f : Nat} {c : Char} {cs : List Char}
    (h1 : c ≠ '-') :
    parseMisc (f + 1) ('<' :: '!' :: c :: cs) =
      some ([], '<' :: '!' :: c :: cs) :=
  parseMisc_stop_two (by decide) h1

/-- The prolog reader stops at a character that is neither
    whitespace nor a less sign. -/
theorem parseMisc_stop_other {f : Nat} {c : Char} {cs : List Char}
    (hw : isWs c = false) (hc : c ≠ '<') :
    parseMisc (f + 1) (c :: cs) = some ([], c :: cs) := by
  have h3 : skipWs (c :: cs) = c :: cs := skipWs_cons hw
  simp [parseMisc, h3, hc]

/-- The element reader refuses a text that does not start with a
    less sign. -/
theorem parseElement_not_lt {f : Nat} {c : Char} {cs : List Char}
    (hc : c ≠ '<') : parseElement f (c :: cs) = none := by
  cases f with
  | zero => rfl
  | succ f =>
    unfold parseElement
    split
    · rename_i rest heq
      exact absurd (List.cons.inj heq).1 hc
    · rfl

/-- The element reader refuses a less sign that a name does not
    follow. -/
theorem parseElement_bad_name {f : Nat} {cs : List Char}
    (h : parseName cs = none) : parseElement f ('<' :: cs) = none := by
  cases f with
  | zero => rfl
  | succ f =>
    unfold parseElement
    split
    · rename_i rest heq
      cases heq
      rw [h]
    · rename_i hne
      exact absurd rfl (hne cs)

theorem parseName_not_start {c : Char} {cs : List Char}
    (h : isNameStart c = false) : parseName (c :: cs) = none := by
  simp [parseName, h]

/-! ## Toolkit: root content -/

/-- The element reader refuses when the start tag is read and the
    content reader refuses. -/
theorem parseElement_content_none {g : Nat} {rest name r1 : List Char}
    {attrs : List (List Char × List Char)} {r2 : List Char}
    (hpn : parseName rest = some (name, r1))
    (hat : parseAttrs g [] r1 = some (attrs, r2, false))
    (hn : parseNodes g r2 = none) : parseElement (g + 1) ('<' :: rest) = none := by
  unfold parseElement
  split
  · rename_i rest' heq
    cases heq
    rw [hpn]
    split
    · rename_i name' r1' heq2
      cases heq2
      rw [hat]
      split
      · rename_i heq3
        cases heq3
      · rename_i attrs' r2' heq3
        cases heq3
        rw [hn]
      · rename_i heq3
        cases heq3
    · rename_i heq2
      cases heq2
  · rename_i hne
    exact absurd rfl (hne rest)

/-- A root start tag with printed attributes and a closing bracket,
    after a printed prolog, is refused when the content reader
    refuses what follows, with its line ends normalized, at every
    fuel from one up. -/
theorem parse_content_none (prolog : List Node) (hpro : MiscOk prolog)
    (name : List Char) (hname : ValidName name)
    (attrs : List (List Char × List Char)) (hattrs : AttrsOk attrs)
    (tail0 : List Char)
    (hcont : ∀ f, 1 ≤ f → parseNodes f (normEol tail0) = none) :
    parse (printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++ '>' :: tail0))) =
      none := by
  have hnn := noCR_validName hname
  obtain ⟨c0, ds, hq, hc0, hds⟩ := hname
  subst hq
  rw [List.cons_append]
  apply parse_root_none prolog hpro c0 _ hc0
  have hds' : '\r' ∉ ds := fun m => hnn (List.mem_cons_of_mem _ m)
  rw [normEol_append_noCR _ _ hds',
    normEol_append_noCR _ _ (noCR_printAttrs attrs hattrs),
    normEol_cons_ne (by decide)]
  generalize normEol tail0 = tail at hcont
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    have hlen : ds.length + (printAttrs attrs).length + tail.length + 2 ≤ g := by
      have h := hf
      simp only [List.length_append, List.length_cons] at h
      omega
    have hpv := printAttrs_length_ge_value attrs
    have hat : parseAttrs g [] (printAttrs attrs ++ '>' :: tail) =
        some (attrs, tail, false) := by
      have h := parseAttrs_print_open attrs [] tail g hattrs
        (by intro kv _ e; simp at e)
        (fun kv hkv => by have := hpv kv hkv; omega)
        (by have := printAttrs_length_ge attrs; omega)
      simpa using h
    have hpn : parseName (c0 :: (ds ++ (printAttrs attrs ++ '>' :: tail))) =
        some (c0 :: ds, printAttrs attrs ++ '>' :: tail) :=
      parseName_append (cs := c0 :: ds) ⟨c0, ds, rfl, hc0, hds⟩
        (printAttrs_head_not_name attrs _ (by
          intro c hc
          simp at hc
          rw [← hc]
          exact isNameChar_false_of not_nameChar_gt))
    exact parseElement_content_none hpn hat (hcont g (by omega))

/-! ## Toolkit: readers that fail -/

/-- Normalizing a text made of two parts is normalizing each part,
    when the second part does not start with a line feed. -/
theorem normEol_append_of_head (A B : List Char) (hB : B.head? ≠ some '\n') :
    normEol (A ++ B) = normEol A ++ normEol B := by
  induction A using normEol.induct with
  | case1 => simp [normEol.eq_1]
  | case2 rest ih =>
    rw [List.cons_append, List.cons_append, normEol.eq_2, normEol.eq_2, ih,
      List.cons_append]
  | case3 rest hrest ih =>
    have hne : ∀ r, rest ++ B ≠ '\n' :: r := by
      intro r e
      cases rest with
      | nil =>
        simp only [List.nil_append] at e
        rw [e] at hB
        exact hB rfl
      | cons x xs =>
        simp only [List.cons_append, List.cons.injEq] at e
        exact hrest xs (by rw [e.1])
    rw [List.cons_append, normEol.eq_3 _ hne, normEol.eq_3 _ hrest, ih,
      List.cons_append]
  | case4 c rest _ hc ih =>
    rw [List.cons_append, normEol_cons_ne hc, normEol_cons_ne hc, ih,
      List.cons_append]

/-- A character of a normalized text is a character of the text,
    or a line feed. -/
theorem normEol_mem (cs : List Char) (x : Char) (h : x ∈ normEol cs) :
    x ∈ cs ∨ x = '\n' := by
  induction cs using normEol.induct with
  | case1 => simp [normEol.eq_1] at h
  | case2 rest ih =>
    rw [normEol.eq_2] at h
    rcases List.mem_cons.mp h with e | h
    · exact Or.inr e
    · rcases ih h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
      · exact Or.inr h
  | case3 rest hrest ih =>
    rw [normEol.eq_3 _ hrest] at h
    rcases List.mem_cons.mp h with e | h
    · exact Or.inr e
    · rcases ih h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
  | case4 c rest _ hc ih =>
    rw [normEol_cons_ne hc] at h
    rcases List.mem_cons.mp h with e | h
    · exact Or.inl (e ▸ List.mem_cons_self)
    · rcases ih h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem normEol_not_mem {cs : List Char} {x : Char} (h : x ∉ cs)
    (hx : x ≠ '\n') : x ∉ normEol cs := by
  intro m
  rcases normEol_mem cs x m with m | e
  · exact h m
  · exact hx e

/-- A text run reader fails on a part with no less sign and no
    ampersand followed by a text it fails on, at every fuel. -/
theorem parseTextRun_fail : ∀ (pre X : List Char), '<' ∉ pre → '&' ∉ pre →
    (∀ f, parseTextRun f X = none) → ∀ f, parseTextRun f (pre ++ X) = none
  | [], X, _, _, hX, f => hX f
  | c :: pre, X, hlt, hamp, hX, f => by
    have hc1 : c ≠ '<' := fun e => hlt (e ▸ List.mem_cons_self)
    have hc2 : c ≠ '&' := fun e => hamp (e ▸ List.mem_cons_self)
    have ih := parseTextRun_fail pre X (fun m => hlt (List.mem_cons_of_mem _ m))
      (fun m => hamp (List.mem_cons_of_mem _ m)) hX
    cases f with
    | zero => rfl
    | succ f =>
      rw [List.cons_append, parseTextRun.eq_3, ite_eq_right hc1, ite_eq_right hc2]
      split
      · split
        · rfl
        · rw [ih f]
          rfl
      · split
        · rw [ih f]
          rfl
        · rfl

/-- The character data reader fails on a text that does not start
    with a less sign and on which the text run reader fails. -/
theorem parseCharData_fail (cs : List Char) (hne : cs ≠ [])
    (hlt : cs.head? ≠ some '<') (hT : ∀ f, parseTextRun f cs = none) :
    ∀ f, parseCharData f cs = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f =>
    unfold parseCharData
    split
    · rename_i heq
      exact absurd heq (by omega)
    · exact absurd rfl hne
    · exact absurd rfl hlt
    · exact absurd rfl hlt
    · rename_i fuel heq _ _ _
      have hf : f = fuel := Nat.succ.inj heq
      subst hf
      rw [hT f]

/-- The content reader fails on a text that does not start with a
    less sign and on which the character data reader fails. -/
theorem parseNodes_fail (cs : List Char) (hne : cs ≠ [])
    (hlt : cs.head? ≠ some '<') (hC : ∀ f, parseCharData f cs = none) :
    ∀ f, parseNodes f cs = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f =>
    unfold parseNodes
    split
    · exact absurd rfl hne
    · exact absurd rfl hlt
    · exact absurd rfl hlt
    · exact absurd rfl hlt
    · exact absurd rfl hlt
    · exact absurd rfl hlt
    · exact absurd rfl hlt
    · rw [hC f]

/-- The head of a text made of a part with no less sign and then a
    text that does not start with a less sign is not a less sign. -/
theorem head_not_lt (A X : List Char) (hA : '<' ∉ A) (hX : X.head? ≠ some '<') :
    (A ++ X).head? ≠ some '<' := by
  cases A with
  | nil => simpa using hX
  | cons a as =>
    intro e
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at e
    exact hA (e ▸ List.mem_cons_self)

/-- Root content that starts with character data (no less sign, no
    ampersand), then a text the text run reader fails on, is
    refused. -/
theorem content_fail (pre X : List Char) (hlt : '<' ∉ pre) (hamp : '&' ∉ pre)
    (hX : X ≠ []) (hXlt : X.head? ≠ some '<')
    (hT : ∀ f, parseTextRun f X = none) :
    ∀ f, 1 ≤ f → parseNodes f (pre ++ X) = none := by
  intro f _
  apply parseNodes_fail
  · intro e
    exact hX (List.append_eq_nil_iff.mp e).2
  · exact head_not_lt pre X hlt hXlt
  · apply parseCharData_fail
    · intro e
      exact hX (List.append_eq_nil_iff.mp e).2
    · exact head_not_lt pre X hlt hXlt
    · exact parseTextRun_fail pre X hlt hamp hT

/-! ## Undefined entities and bad character references -/

theorem not_nameChar_semicolon : ¬ IsNameChar ';' :=
  not_nameChar_of_test (by decide)

theorem noSemi_validName {cs : List Char} (h : ValidName cs) : ';' ∉ cs := by
  obtain ⟨c, ds, rfl, hc, hds⟩ := h
  intro m
  rcases List.mem_cons.mp m with e | e
  · exact not_nameChar_semicolon (e ▸ IsNameStart.toNameChar hc)
  · exact not_nameChar_semicolon (hds _ e)

theorem eq_of_append_semicolon : ∀ (w e post rest : List Char), ';' ∉ e →
    ';' ∉ w → e ++ ';' :: post = w ++ ';' :: rest → e = w
  | [], e, post, rest, he, _, h => by
    cases e with
    | nil => rfl
    | cons x xs =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd (by rw [← h.1]; exact List.mem_cons_self) he
  | x :: w, e, post, rest, he, hw, h => by
    cases e with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by rw [h.1]; exact List.mem_cons_self) hw
    | cons y e' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      rw [eq_of_append_semicolon w e' post rest
        (fun m => he (List.mem_cons_of_mem _ m))
        (fun m => hw (List.mem_cons_of_mem _ m)) h2]

/-- The names of the five predefined entities. -/
abbrev fiveEntities : List (List Char) :=
  [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
    ['q', 'u', 'o', 't']]

/-- The reference reader refuses a reference to any valid name other
    than the five predefined entities, whatever follows it. -/
theorem parseRef_undefined (e post : List Char) (he : ValidName e)
    (hfive : e ∉ fiveEntities) : parseRef (e ++ ';' :: post) = none := by
  have hsemi : ';' ∉ e := noSemi_validName he
  unfold parseRef
  split
  · rename_i rest heq
    have := eq_of_append_semicolon ['l', 't'] e post rest hsemi (by decide) heq
    exact absurd (by rw [this]; decide) hfive
  · rename_i rest heq
    have := eq_of_append_semicolon ['g', 't'] e post rest hsemi (by decide) heq
    exact absurd (by rw [this]; decide) hfive
  · rename_i rest heq
    have := eq_of_append_semicolon ['a', 'm', 'p'] e post rest hsemi (by decide) heq
    exact absurd (by rw [this]; decide) hfive
  · rename_i rest heq
    have := eq_of_append_semicolon ['a', 'p', 'o', 's'] e post rest hsemi
      (by decide) heq
    exact absurd (by rw [this]; decide) hfive
  · rename_i rest heq
    have := eq_of_append_semicolon ['q', 'u', 'o', 't'] e post rest hsemi
      (by decide) heq
    exact absurd (by rw [this]; decide) hfive
  · rename_i rest heq
    obtain ⟨c, ds, rfl, hc, _⟩ := he
    simp only [List.cons_append, List.cons.injEq] at heq
    exact absurd heq.1 (IsNameStart.ne_of_test hc (by decide))
  · rfl

theorem textRun_undefined (e post : List Char) (he : ValidName e)
    (hfive : e ∉ fiveEntities) :
    ∀ f, parseTextRun f ('&' :: (e ++ ';' :: post)) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f =>
    rw [parseTextRun.eq_3, ite_eq_right (by decide), ite_eq_left rfl,
      parseRef_undefined e post he hfive]

theorem textRun_surrogate (post : List Char) :
    ∀ f, parseTextRun f
      ('&' :: '#' :: 'x' :: 'D' :: '8' :: '0' :: '0' :: ';' :: post) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f => rfl

theorem textRun_zero (post : List Char) :
    ∀ f, parseTextRun f ('&' :: '#' :: '0' :: ';' :: post) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f => rfl

theorem textRun_cdata_close (post : List Char) :
    ∀ f, parseTextRun f (']' :: ']' :: '>' :: post) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f => rfl

/-- Normalizing a text run that ends in a fixed tail with no carriage
    return and no leading line feed. -/
theorem normEol_pre_tail (pre T : List Char) (hT : '\r' ∉ T)
    (hh : T.head? ≠ some '\n') : normEol (pre ++ T) = normEol pre ++ T := by
  rw [normEol_append_of_head _ _ hh, normEol_of_noCR _ hT]

/-! ## Attribute values that fail -/

/-- The attribute value reader fails on a part with no double quote
    and no ampersand followed by a text it fails on. -/
theorem parseAttrValue_fail : ∀ (pre X : List Char), '"' ∉ pre → '&' ∉ pre →
    (∀ f, parseAttrValue '"' f X = none) →
    ∀ f, parseAttrValue '"' f (pre ++ X) = none
  | [], X, _, _, hX, f => hX f
  | c :: pre, X, hq, hamp, hX, f => by
    have hc1 : c ≠ '"' := fun e => hq (e ▸ List.mem_cons_self)
    have hc2 : c ≠ '&' := fun e => hamp (e ▸ List.mem_cons_self)
    have ih := parseAttrValue_fail pre X (fun m => hq (List.mem_cons_of_mem _ m))
      (fun m => hamp (List.mem_cons_of_mem _ m)) hX
    cases f with
    | zero => rfl
    | succ f =>
      rw [List.cons_append, parseAttrValue.eq_3, ite_eq_right hc1]
      split
      · rfl
      · split
        · rw [ih f]
          rfl
        · split
          · rw [ih f]
            rfl
          · rfl

theorem attrValue_lt (rest : List Char) :
    ∀ f, parseAttrValue '"' f ('<' :: rest) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f => rfl

theorem attrValue_undefined (e post : List Char) (he : ValidName e)
    (hfive : e ∉ fiveEntities) :
    ∀ f, parseAttrValue '"' f ('&' :: (e ++ ';' :: post)) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f =>
    rw [parseAttrValue.eq_3, ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_left rfl, parseRef_undefined e post he hfive]

/-! ## One attribute step -/

theorem AttrsOk_mem : ∀ (attrs : List (List Char × List Char))
    (kv : List Char × List Char), AttrsOk attrs → kv ∈ attrs →
    ValidName kv.1 ∧ kv.1 ≠ xmlnsName
  | [], _, _, h => absurd h List.not_mem_nil
  | kv0 :: rest, kv, hok, h => by
    rcases List.mem_cons.mp h with e | h
    · subst e
      exact ⟨hok.1, hok.2.1⟩
    · exact AttrsOk_mem rest kv hok.2.2.2.2 h

/-- The attribute reader at a space, a valid name, an equals sign
    and a double quote: it refuses when the value reader refuses, or
    when the name is already among the attributes read. -/
theorem parseAttrs_dq_none (g : Nat) (acc : List (List Char × List Char))
    (a W : List Char) (ha : ValidName a)
    (H : ∀ v r4, parseAttrValue '"' g W = some (v, r4) →
      (acc.any fun kv => decide (kv.1 = a)) = true) :
    parseAttrs (g + 1) acc (' ' :: (a ++ '=' :: '"' :: W)) = none := by
  obtain ⟨c0, ds, rfl, hc0, hds⟩ := ha
  have hw0 : isWs c0 = false := isWs_false_of_not (IsNameStart.ne_ws hc0)
  have hsk : skipWs (' ' :: ((c0 :: ds) ++ '=' :: '"' :: W)) =
      c0 :: (ds ++ '=' :: '"' :: W) := by
    rw [List.cons_append, skipWs.eq_2, ite_eq_left (by decide)]
    exact skipWs_cons hw0
  have hpn : parseName (c0 :: (ds ++ '=' :: '"' :: W)) =
      some (c0 :: ds, '=' :: '"' :: W) :=
    parseName_append (cs := c0 :: ds) ⟨c0, ds, rfl, hc0, hds⟩ (by
      intro c hc
      simp at hc
      rw [← hc]
      exact isNameChar_false_of not_nameChar_eq)
  rw [parseAttrs.eq_2, hsk]
  split
  · rename_i rest heq
    exact absurd (List.cons.inj heq).1 (IsNameStart.ne_slash hc0)
  · rename_i rest heq
    exact absurd (List.cons.inj heq).1 (IsNameStart.ne_of_test hc0 (by decide))
  · rename_i c tl _ _ heq
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    rw [ite_eq_left (by simp [isNameStart_of hc0, startsWithWs, isWs]), hpn]
    split
    · rename_i aname r1 heq2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq2)
      split
      · rfl
      · rw [skipWs_cons (by decide : isWs '=' = false)]
        split
        · rename_i r2 heq3
          obtain ⟨_, rfl⟩ := List.cons.inj heq3
          rw [skipWs_cons (by decide : isWs '"' = false)]
          split
          · rename_i r3 heq4
            obtain ⟨_, rfl⟩ := List.cons.inj heq4
            split
            · rename_i v r4 hv
              rw [ite_eq_left (H v r4 hv)]
            · rfl
          · rename_i r3 heq4
            exact absurd (List.cons.inj heq4).1 (by decide)
          · rfl
        · rfl
    · rename_i heq2
      cases heq2
  · rename_i heq
    cases heq

/-- The attribute reader at a space, a valid name, an equals sign
    and a character that is no quote and no whitespace: refused. -/
theorem parseAttrs_unquoted_none (g : Nat) (acc : List (List Char × List Char))
    (a : List Char) (c : Char) (W : List Char) (ha : ValidName a)
    (hc1 : c ≠ '"') (hc2 : c ≠ '\'') (hcw : isWs c = false) :
    parseAttrs (g + 1) acc (' ' :: (a ++ '=' :: c :: W)) = none := by
  obtain ⟨c0, ds, rfl, hc0, hds⟩ := ha
  have hw0 : isWs c0 = false := isWs_false_of_not (IsNameStart.ne_ws hc0)
  have hsk : skipWs (' ' :: ((c0 :: ds) ++ '=' :: c :: W)) =
      c0 :: (ds ++ '=' :: c :: W) := by
    rw [List.cons_append, skipWs.eq_2, ite_eq_left (by decide)]
    exact skipWs_cons hw0
  have hpn : parseName (c0 :: (ds ++ '=' :: c :: W)) =
      some (c0 :: ds, '=' :: c :: W) :=
    parseName_append (cs := c0 :: ds) ⟨c0, ds, rfl, hc0, hds⟩ (by
      intro x hx
      simp at hx
      rw [← hx]
      exact isNameChar_false_of not_nameChar_eq)
  rw [parseAttrs.eq_2, hsk]
  split
  · rename_i rest heq
    exact absurd (List.cons.inj heq).1 (IsNameStart.ne_slash hc0)
  · rename_i rest heq
    exact absurd (List.cons.inj heq).1 (IsNameStart.ne_of_test hc0 (by decide))
  · rename_i c' tl _ _ heq
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    rw [ite_eq_left (by simp [isNameStart_of hc0, startsWithWs, isWs]), hpn]
    split
    · rename_i aname r1 heq2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq2)
      split
      · rfl
      · rw [skipWs_cons (by decide : isWs '=' = false)]
        split
        · rename_i r2 heq3
          obtain ⟨_, rfl⟩ := List.cons.inj heq3
          rw [skipWs_cons hcw]
          split
          · rename_i r3 heq4
            exact absurd (List.cons.inj heq4).1 hc1
          · rename_i r3 heq4
            exact absurd (List.cons.inj heq4).1 hc2
          · rfl
        · rfl
    · rename_i heq2
      cases heq2
  · rename_i heq
    cases heq

/-- The attribute reader refuses a text that starts with a
    character that is no whitespace, no slash and no closing
    bracket: an attribute needs whitespace before it. -/
theorem parseAttrs_head_none (f : Nat) (hf : 1 ≤ f)
    (acc : List (List Char × List Char)) (c : Char) (rest : List Char)
    (hw : isWs c = false) (h1 : c ≠ '/') (h2 : c ≠ '>') :
    parseAttrs f acc (c :: rest) = none := by
  cases f with
  | zero => omega
  | succ g =>
    rw [parseAttrs.eq_2, skipWs_cons hw]
    split
    · rename_i r heq
      exact absurd (List.cons.inj heq).1 h1
    · rename_i r heq
      exact absurd (List.cons.inj heq).1 h2
    · rename_i c' tl _ _ heq
      obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      rw [ite_eq_right (by simp [startsWithWs, hw])]
    · rename_i heq
      cases heq

/-! ## Element-level helpers -/

/-- The element reader refuses when the end tag names another
    element. -/
theorem parseElement_mismatch {g : Nat} {rest name r1 : List Char}
    {attrs : List (List Char × List Char)} {r2 : List Char}
    {content : List Node} {other R : List Char}
    (hpn : parseName rest = some (name, r1))
    (hat : parseAttrs g [] r1 = some (attrs, r2, false))
    (hn : parseNodes g r2 = some (content, '<' :: '/' :: (other ++ '>' :: R)))
    (hon : parseName (other ++ '>' :: R) = some (other, '>' :: R))
    (hne : other ≠ name) :
    parseElement (g + 1) ('<' :: rest) = none := by
  unfold parseElement
  split
  · rename_i rest' heq
    cases heq
    rw [hpn]
    split
    · rename_i name' r1' heq2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq2)
      rw [hat]
      split
      · rename_i heq3
        cases heq3
      · rename_i attrs' r2' heq3
        cases heq3
        rw [hn]
        split
        · rename_i content' r3 heq4
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq4)
          split
          · rename_i r4 heq5
            obtain ⟨-, heq5⟩ := List.cons.inj heq5
            obtain ⟨-, rfl⟩ := List.cons.inj heq5
            rw [hon]
            split
            · rename_i ename r5 heq6
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq6)
              rw [skipWs_cons (by decide : isWs '>' = false)]
              split
              · rw [ite_eq_right hne]
              · rfl
            · rename_i heq6
              cases heq6
          · rename_i hne'
            exact absurd rfl (hne' _)
        · rename_i heq4
          cases heq4
      · rename_i heq3
        cases heq3
    · rename_i heq2
      cases heq2
  · rename_i hne'
    exact absurd rfl (hne' rest)

/-- The element reader refuses when the content reader stops at the
    end of the text, with no end tag. -/
theorem parseElement_unclosed {g : Nat} {rest name r1 : List Char}
    {attrs : List (List Char × List Char)} {r2 : List Char}
    (hpn : parseName rest = some (name, r1))
    (hat : parseAttrs g [] r1 = some (attrs, r2, false))
    (hn : ∀ ns r3, parseNodes g r2 = some (ns, r3) → r3 = []) :
    parseElement (g + 1) ('<' :: rest) = none := by
  unfold parseElement
  split
  · rename_i rest' heq
    cases heq
    rw [hpn]
    split
    · rename_i name' r1' heq2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq2)
      rw [hat]
      split
      · rename_i heq3
        cases heq3
      · rename_i attrs' r2' heq3
        cases heq3
        split
        · rename_i content r3 hc
          have := hn content r3 hc
          subst this
          rfl
        · rfl
      · rename_i heq3
        cases heq3
    · rename_i heq2
      cases heq2
  · rename_i hne'
    exact absurd rfl (hne' rest)

/-- A comment body reader refuses a body a well formed comment may
    hold followed by two dashes and anything but a closing bracket. -/
theorem parseCommentBody_dashdash : ∀ (body Z : List Char),
    NoDashDash body → NotDashEnd body → (∀ c ∈ body, LegalChar c) →
    Z.head? ≠ some '>' → parseCommentBody (body ++ '-' :: '-' :: Z) = none
  | [], Z, _, _, _, hZ => by
    rw [List.nil_append]
    unfold parseCommentBody
    rw [ite_eq_left rfl]
    split
    · rename_i r heq
      obtain ⟨-, rfl⟩ := List.cons.inj heq
      exact absurd rfl hZ
    · rfl
    · rename_i h1 h2
      exact absurd rfl (h2 Z)
  | c :: body, Z, hdd, hde, hlegal, hZ => by
    have hlegal' : ∀ x ∈ body, LegalChar x :=
      fun x hx => hlegal x (List.mem_cons_of_mem c hx)
    have hdd' : NoDashDash body := by
      intro pre suf h
      exact hdd (c :: pre) suf (by simp [h])
    have hde' : NotDashEnd body := by
      intro pre h
      exact hde (c :: pre) (by simp [h])
    have ih := parseCommentBody_dashdash body Z hdd' hde' hlegal' hZ
    by_cases hc : c = '-'
    · subst hc
      cases body with
      | nil => exact absurd rfl (hde [])
      | cons d ds =>
        have hd : d ≠ '-' := by
          intro e
          subst e
          exact hdd [] ds (by simp)
        rw [List.cons_append, List.cons_append, parseCommentBody_dash_cons hd,
          ← List.cons_append, ih]
        rfl
    · rw [List.cons_append]
      unfold parseCommentBody
      rw [ite_eq_right hc, ite_eq_left (isLegalChar_of (hlegal c List.mem_cons_self)),
        ih]
      rfl

/-- The content reader at `<!--` refuses when the comment body
    reader refuses. Stated with the three characters after the less
    sign as variables: a matcher over character literals, applied to
    a text of literals that differ from its patterns, makes the
    nanoda kernel recurse past its stack; variables keep every
    literal comparison out of the matcher. -/
theorem parseNodes_comment_none' (a b c : Char) (B : List Char)
    (ha : a = '!') (hb : b = '-')
    (hB : parseCommentBody B = none) (f : Nat) :
    parseNodes (f + 1) ('<' :: a :: b :: c :: B) = none := by
  unfold parseNodes
  split
  · rename_i heq
    cases heq
  · rename_i t heq
    have e := (List.cons.inj (List.cons.inj heq).2).1
    rw [ha] at e
    exact absurd e (by decide)
  · rename_i rest heq
    obtain ⟨-, heq⟩ := List.cons.inj heq
    obtain ⟨-, heq⟩ := List.cons.inj heq
    obtain ⟨-, heq⟩ := List.cons.inj heq
    obtain ⟨-, rfl⟩ := List.cons.inj heq
    rw [hB]
  · rename_i t heq
    have e := (List.cons.inj (List.cons.inj (List.cons.inj heq).2).2).1
    rw [hb] at e
    exact absurd e (by decide)
  · rename_i rest heq
    have e := (List.cons.inj (List.cons.inj heq).2).1
    rw [ha] at e
    exact absurd e (by decide)
  · rename_i c' t _ _ _ _ heq
    obtain ⟨-, heq⟩ := List.cons.inj heq
    obtain ⟨rfl, -⟩ := List.cons.inj heq
    rw [ite_eq_right (by rw [ha]; decide)]
  · rename_i heq
    exact absurd (List.cons.inj heq).2 (by simp)
  · rename_i _ _ _ _ _ h6 _
    exact absurd rfl (h6 a _)

theorem parseNodes_comment_none (B : List Char) (hB : parseCommentBody B = none) :
    ∀ f, parseNodes f ('<' :: '!' :: '-' :: '-' :: B) = none := by
  intro f
  cases f with
  | zero => rfl
  | succ f => exact parseNodes_comment_none' '!' '-' '-' B rfl rfl hB f

/-- The prolog reader at `<?` refuses when the processing
    instruction reader refuses, with both marks as variables for the
    same reason. -/
theorem parseMisc_pi_none (a c : Char) (X : List Char) (ha : a = '<')
    (hc : c = '?') (hpi : parsePI X = none) (f : Nat) :
    parseMisc (f + 1) (a :: c :: X) = none := by
  have hw : isWs a = false := by rw [ha]; decide
  unfold parseMisc
  dsimp only
  rw [skipWs_cons hw]
  split
  · rename_i r heq
    have e := (List.cons.inj (List.cons.inj heq).2).1
    rw [hc] at e
    exact absurd e (by decide)
  · rename_i r heq
    obtain ⟨-, heq⟩ := List.cons.inj heq
    obtain ⟨-, rfl⟩ := List.cons.inj heq
    rw [hpi]
  · rename_i h1 h2
    exact absurd (by rw [ha, hc]) (h2 X)

/-! ## The refusal theorems -/

/-- After a printed prolog, `<!` followed by anything but a dash is
    refused. -/
theorem parse_bang_none (prolog : List Node) (hpro : MiscOk prolog)
    (c : Char) (rest : List Char) (h1 : c ≠ '-') (h2 : c ≠ '\r') :
    parse (printNodes prolog ++ '<' :: '!' :: c :: rest) = none := by
  have hn : normEol ('<' :: '!' :: c :: rest) = '<' :: '!' :: c :: normEol rest := by
    rw [normEol_cons_ne (by decide), normEol_cons_ne (by decide),
      normEol_cons_ne h2]
  apply parse_prolog_none prolog hpro
  · intro f hf
    rw [hn, skipWs_cons (by decide)]
    cases f with
    | zero => omega
    | succ f =>
      exact parseMisc_stop_bang h1
  · intro f _
    rw [hn, skipWs_cons (by decide)]
    exact parseElement_bad_name (parseName_not_start (by decide))

theorem rejects_doctype (prolog : List Node) (rest : List Char)
    (hpro : MiscOk prolog) :
    parse (printNodes prolog ++ ['<', '!', 'D', 'O', 'C', 'T', 'Y', 'P', 'E'] ++
      rest) = none := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact parse_bang_none prolog hpro 'D' _ (by decide) (by decide)

theorem rejects_cdata_in_prolog (prolog : List Node) (rest : List Char)
    (hpro : MiscOk prolog) :
    parse (printNodes prolog ++ ['<', '!', '[', 'C', 'D', 'A', 'T', 'A', '['] ++
      rest) = none := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact parse_bang_none prolog hpro '[' _ (by decide) (by decide)

theorem rejects_text_before_root (prolog : List Node) (c : Char)
    (rest : List Char) (hpro : MiscOk prolog) (hws : ¬ IsWs c)
    (hlt : c ≠ '<') : parse (printNodes prolog ++ c :: rest) = none := by
  have hw : isWs c = false := isWs_false_of_not hws
  have hcr : c ≠ '\r' := fun e => hws (Or.inr (Or.inr (Or.inr e)))
  have hn : normEol (c :: rest) = c :: normEol rest := normEol_cons_ne hcr rest
  apply parse_prolog_none prolog hpro
  · intro f hf
    rw [hn, skipWs_cons hw]
    cases f with
    | zero => omega
    | succ f => exact parseMisc_stop_other hw hlt
  · intro f _
    rw [hn, skipWs_cons hw]
    exact parseElement_not_lt hlt

theorem rejects_digit_name (prolog : List Node) (d : Char) (rest : List Char)
    (hpro : MiscOk prolog)
    (hd : d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) :
    parse (printNodes prolog ++ '<' :: d :: rest) = none := by
  have hfacts : d ≠ '\r' ∧ d ≠ '?' ∧ d ≠ '!' ∧ isNameStart d = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  obtain ⟨h1, h2, h3, h4⟩ := hfacts
  have hn : normEol ('<' :: d :: rest) = '<' :: d :: normEol rest := by
    rw [normEol_cons_ne (by decide), normEol_cons_ne h1]
  apply parse_prolog_none prolog hpro
  · intro f hf
    rw [hn, skipWs_cons (by decide)]
    cases f with
    | zero => omega
    | succ f =>
      exact parseMisc_stop_lt h3 h2
  · intro f _
    rw [hn, skipWs_cons (by decide)]
    exact parseElement_bad_name (parseName_not_start h4)

theorem rejects_colon_in_name (prolog : List Node) (name rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) :
    parse (printNodes prolog ++ '<' :: name ++ ':' :: rest) = none := by
  have e : printNodes prolog ++ '<' :: name ++ ':' :: rest =
      printNodes prolog ++ '<' :: (name ++ (printAttrs [] ++ ':' :: rest)) := by
    simp [printAttrs, List.append_assoc]
  rw [e]
  have hn : normEol (':' :: rest) = ':' :: normEol rest :=
    normEol_cons_ne (by decide) rest
  apply parse_attrs_none prolog hpro name hname [] trivial
  · rw [hn]
    intro c hc
    simp [printAttrs] at hc
    rw [← hc]
    decide
  · intro f hf
    rw [hn]
    exact parseAttrs_head_none f hf [] ':' _ (by decide) (by decide) (by decide)

/-- Content of the root that starts with character data and then a
    fixed tail the text run reader fails on: the generic step. -/
theorem rejects_in_text (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre T post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre)
    (hT : '\r' ∉ T) (hTne : T ≠ []) (hTh1 : T.head? ≠ some '\n')
    (hTh2 : T.head? ≠ some '<')
    (hfail : ∀ R f, parseTextRun f (T ++ R) = none) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      T ++ post) = none := by
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      T ++ post = printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++
        '>' :: (pre ++ (T ++ post)))) := by
    simp [List.append_assoc]
  rw [e]
  apply parse_content_none prolog hpro name hname attrs hattrs
  have hh : (T ++ post).head? ≠ some '\n' := by
    cases T with
    | nil => exact absurd rfl hTne
    | cons t ts => simpa using hTh1
  rw [normEol_append_of_head _ _ hh, normEol_append_noCR _ _ hT]
  apply content_fail (normEol pre) (T ++ normEol post)
    (normEol_not_mem hlt (by decide)) (normEol_not_mem hamp (by decide))
  · intro e
    exact hTne (List.append_eq_nil_iff.mp e).1
  · cases T with
    | nil => exact absurd rfl hTne
    | cons t ts => simpa using hTh2
  · exact hfail (normEol post)

theorem rejects_undefined_entity (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre e post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) (he : ValidName e)
    (hfive : e ∉ [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
      ['q', 'u', 'o', 't']]) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      '&' :: e ++ ';' :: post) = none := by
  have e1 : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      '&' :: e ++ ';' :: post = printNodes prolog ++ '<' :: name ++
        printAttrs attrs ++ '>' :: pre ++ ('&' :: e ++ [';']) ++ post := by
    simp [List.append_assoc]
  rw [e1]
  apply rejects_in_text prolog name attrs pre _ post hpro hname hattrs hlt hamp
  · intro m
    rcases List.mem_cons.mp m with h | m
    · cases h
    · rcases List.mem_append.mp m with m | m
      · exact noCR_validName he m
      · simp at m
  · simp
  · simp
  · simp
  · intro R f
    rw [List.append_assoc, List.cons_append, List.singleton_append]
    exact textRun_undefined e R he hfive f

theorem rejects_surrogate_ref (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      ['&', '#', 'x', 'D', '8', '0', '0', ';'] ++ post) = none :=
  rejects_in_text prolog name attrs pre _ post hpro hname hattrs hlt hamp
    (by decide) (by simp) (by decide) (by decide)
    (fun R f => textRun_surrogate R f)

theorem rejects_zero_ref (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      ['&', '#', '0', ';'] ++ post) = none :=
  rejects_in_text prolog name attrs pre _ post hpro hname hattrs hlt hamp
    (by decide) (by simp) (by decide) (by decide)
    (fun R f => textRun_zero R f)

theorem rejects_cdata_close_in_text (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (pre post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hlt : '<' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' :: pre ++
      [']', ']', '>'] ++ post) = none :=
  rejects_in_text prolog name attrs pre _ post hpro hname hattrs hlt hamp
    (by decide) (by simp) (by decide) (by decide)
    (fun R f => textRun_cdata_close R f)

/-- An attribute of the root, after printed attributes, whose value
    the value reader refuses: the generic step. -/
theorem rejects_in_value (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a V : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a)
    (hfail : ∀ f, parseAttrValue '"' f (normEol V) = none) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: V) = none := by
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: V = printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++
        ' ' :: (a ++ '=' :: '"' :: V))) := by
    simp [List.append_assoc]
  rw [e]
  have hn : normEol (' ' :: (a ++ '=' :: '"' :: V)) =
      ' ' :: (a ++ '=' :: '"' :: normEol V) := by
    rw [normEol_cons_ne (by decide), normEol_append_noCR _ _ (noCR_validName ha),
      normEol_cons_ne (by decide), normEol_cons_ne (by decide)]
  apply parse_attrs_none prolog hpro name hname attrs hattrs
  · rw [hn]
    apply printAttrs_head_not_name
    intro c hc
    simp at hc
    rw [← hc]
    exact isNameChar_false_of not_nameChar_space
  · intro f hf
    rw [hn]
    cases f with
    | zero => omega
    | succ g =>
      apply parseAttrs_dq_none g attrs a _ ha
      intro v r4 h
      rw [hfail g] at h
      cases h

theorem rejects_undefined_entity_in_attribute (prolog : List Node)
    (name : List Char) (attrs : List (List Char × List Char))
    (a pre e post : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hq : '"' ∉ pre) (hamp : '&' ∉ pre) (he : ValidName e)
    (hfive : e ∉ [['l', 't'], ['g', 't'], ['a', 'm', 'p'], ['a', 'p', 'o', 's'],
      ['q', 'u', 'o', 't']]) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '&' :: e ++ ';' :: post) = none := by
  have e1 : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '&' :: e ++ ';' :: post =
      printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: (pre ++ '&' :: (e ++ ';' :: post)) := by
    simp [List.append_assoc]
  rw [e1]
  apply rejects_in_value prolog name attrs a _ hpro hname hattrs ha
  rw [normEol_append_of_head _ _ (by simp), normEol_cons_ne (by decide),
    normEol_append_noCR _ _ (noCR_validName he), normEol_cons_ne (by decide)]
  exact parseAttrValue_fail (normEol pre) _ (normEol_not_mem hq (by decide))
    (normEol_not_mem hamp (by decide)) (attrValue_undefined e _ he hfive)

theorem rejects_lt_in_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a pre rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hq : '"' ∉ pre) (hamp : '&' ∉ pre) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '<' :: rest) = none := by
  have e1 : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: pre ++ '<' :: rest =
      printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: '"' :: (pre ++ '<' :: rest) := by
    simp [List.append_assoc]
  rw [e1]
  apply rejects_in_value prolog name attrs a _ hpro hname hattrs ha
  rw [normEol_append_of_head _ _ (by simp), normEol_cons_ne (by decide)]
  exact parseAttrValue_fail (normEol pre) _ (normEol_not_mem hq (by decide))
    (normEol_not_mem hamp (by decide)) (attrValue_lt _)

theorem rejects_unquoted_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a : List Char) (c : Char)
    (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (ha : ValidName a) (hc1 : c ≠ '"') (hc2 : c ≠ '\'') (hcw : ¬ IsWs c) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: c :: rest) = none := by
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ' ' :: a ++
      '=' :: c :: rest = printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++
        ' ' :: (a ++ '=' :: c :: rest))) := by
    simp [List.append_assoc]
  rw [e]
  have hcr : c ≠ '\r' := fun e => hcw (Or.inr (Or.inr (Or.inr e)))
  have hn : normEol (' ' :: (a ++ '=' :: c :: rest)) =
      ' ' :: (a ++ '=' :: c :: normEol rest) := by
    rw [normEol_cons_ne (by decide), normEol_append_noCR _ _ (noCR_validName ha),
      normEol_cons_ne (by decide), normEol_cons_ne hcr]
  apply parse_attrs_none prolog hpro name hname attrs hattrs
  · rw [hn]
    apply printAttrs_head_not_name
    intro x hx
    simp at hx
    rw [← hx]
    exact isNameChar_false_of not_nameChar_space
  · intro f hf
    rw [hn]
    cases f with
    | zero => omega
    | succ g =>
      exact parseAttrs_unquoted_none g attrs a c _ ha hc1 hc2
        (isWs_false_of_not hcw)

theorem noCR_printAttrs_one (a v : List Char) (ha : ValidName a) :
    '\r' ∉ printAttrs [(a, v)] := by
  have h1 := noCR_validName ha
  have h2 := noCR_escapeAttr v
  simp [printAttrs, h1, h2]

theorem rejects_duplicate_attribute (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (a v rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hdup : ∃ w, (a, w) ∈ attrs) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      printAttrs [(a, v)] ++ rest) = none := by
  obtain ⟨w, hw⟩ := hdup
  obtain ⟨ha, _⟩ := AttrsOk_mem attrs (a, w) hattrs hw
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++
      printAttrs [(a, v)] ++ rest = printNodes prolog ++ '<' :: (name ++
        (printAttrs attrs ++ (printAttrs [(a, v)] ++ rest))) := by
    simp [List.append_assoc]
  rw [e]
  have hn : normEol (printAttrs [(a, v)] ++ rest) =
      printAttrs [(a, v)] ++ normEol rest :=
    normEol_append_noCR _ _ (noCR_printAttrs_one a v ha)
  apply parse_attrs_none prolog hpro name hname attrs hattrs
  · rw [hn]
    apply printAttrs_head_not_name
    intro c hc
    simp [printAttrs] at hc
    rw [← hc]
    exact isNameChar_false_of not_nameChar_space
  · intro f hf
    rw [hn]
    cases f with
    | zero => omega
    | succ g =>
      have e2 : printAttrs [(a, v)] ++ normEol rest =
          ' ' :: (a ++ '=' :: '"' :: (escapeAttr v ++ '"' :: normEol rest)) := by
        simp [printAttrs, List.append_assoc]
      rw [e2]
      apply parseAttrs_dq_none g attrs a _ ha
      intro v' r4 _
      exact List.any_eq_true.mpr ⟨(a, w), hw, by simp⟩

theorem rejects_dashdash_in_comment (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (body : List Char) (c : Char)
    (rest : List Char)
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs)
    (hbody : WFNode (.comment body)) (hc : c ≠ '>') :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
      '<' :: '!' :: '-' :: '-' :: body ++ '-' :: '-' :: c :: rest) = none := by
  cases hbody with
  | comment hdd hde hlegal hcr =>
    have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
        '<' :: '!' :: '-' :: '-' :: body ++ '-' :: '-' :: c :: rest =
        printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++ '>' ::
          ('<' :: '!' :: '-' :: '-' :: (body ++ '-' :: '-' :: c :: rest)))) := by
      simp [List.append_assoc]
    rw [e]
    apply parse_content_none prolog hpro name hname attrs hattrs
    rw [normEol_cons_ne (by decide), normEol_cons_ne (by decide),
      normEol_cons_ne (by decide), normEol_cons_ne (by decide),
      normEol_append_noCR _ _ hcr, normEol_cons_ne (by decide),
      normEol_cons_ne (by decide)]
    intro f _
    apply parseNodes_comment_none
    apply parseCommentBody_dashdash body _ hdd hde hlegal
    intro h
    rcases normEol_head (c :: rest) '>' h with h | h
    · exact hc (Option.some.inj h)
    · cases h

theorem rejects_mismatched_tags (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char)) (content : List Node)
    (other rest : List Char)
    (hpro : MiscOk prolog) (hel : WFNode (.elem name attrs content))
    (hother : ValidName other) (hne : other ≠ name) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
      printNodes content ++ '<' :: '/' :: other ++ '>' :: rest) = none := by
  cases hel with
  | elem hname hattrs hcontent =>
    have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ '>' ::
        printNodes content ++ '<' :: '/' :: other ++ '>' :: rest =
        printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++ '>' ::
          (printNodes content ++ '<' :: '/' :: (other ++ '>' :: rest)))) := by
      simp [List.append_assoc]
    rw [e]
    have hnn := noCR_validName hname
    obtain ⟨c0, ds, hq, hc0, hds⟩ := hname
    subst hq
    rw [List.cons_append]
    apply parse_root_none prolog hpro c0 _ hc0
    have hds' : '\r' ∉ ds := fun m => hnn (List.mem_cons_of_mem _ m)
    rw [normEol_append_noCR _ _ hds',
      normEol_append_noCR _ _ (noCR_printAttrs attrs hattrs),
      normEol_cons_ne (by decide),
      normEol_append_noCR _ _ (noCR_printNodes content hcontent),
      normEol_cons_ne (by decide), normEol_cons_ne (by decide),
      normEol_append_noCR _ _ (noCR_validName hother),
      normEol_cons_ne (by decide)]
    generalize normEol rest = R
    intro f hf
    cases f with
    | zero => omega
    | succ g =>
      have hlen : ds.length + (printAttrs attrs).length +
          (printNodes content).length + other.length + R.length + 4 ≤ g := by
        have h := hf
        simp only [List.length_append, List.length_cons] at h
        omega
      have hpv := printAttrs_length_ge_value attrs
      have hat : parseAttrs g [] (printAttrs attrs ++ '>' ::
          (printNodes content ++ '<' :: '/' :: (other ++ '>' :: R))) =
          some (attrs, printNodes content ++ '<' :: '/' :: (other ++ '>' :: R),
            false) := by
        have h := parseAttrs_print_open attrs []
          (printNodes content ++ '<' :: '/' :: (other ++ '>' :: R)) g hattrs
          (by intro kv _ e; simp at e)
          (fun kv hkv => by have := hpv kv hkv; omega)
          (by have := printAttrs_length_ge attrs; omega)
        simpa using h
      have hpn : parseName (c0 :: (ds ++ (printAttrs attrs ++ '>' ::
          (printNodes content ++ '<' :: '/' :: (other ++ '>' :: R))))) =
          some (c0 :: ds, printAttrs attrs ++ '>' ::
            (printNodes content ++ '<' :: '/' :: (other ++ '>' :: R))) :=
        parseName_append (cs := c0 :: ds) ⟨c0, ds, rfl, hc0, hds⟩
          (printAttrs_head_not_name attrs _ (by
            intro c hc
            simp at hc
            rw [← hc]
            exact isNameChar_false_of not_nameChar_gt))
      have hn : parseNodes g (printNodes content ++ '<' :: '/' :: (other ++ '>' :: R)) =
          some (content, '<' :: '/' :: (other ++ '>' :: R)) :=
        (elem_nodes ((printNodes content).length + 2)).2 g (by omega) content
          (other ++ '>' :: R) hcontent rfl
      have hon : parseName (other ++ '>' :: R) = some (other, '>' :: R) :=
        parseName_append hother (by
          intro c hc
          simp at hc
          rw [← hc]
          exact isNameChar_false_of not_nameChar_gt)
      exact parseElement_mismatch hpn hat hn hon hne

theorem rejects_unclosed_element (prolog : List Node) (name : List Char)
    (attrs : List (List Char × List Char))
    (hpro : MiscOk prolog) (hname : ValidName name) (hattrs : AttrsOk attrs) :
    parse (printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ['>']) =
      none := by
  have e : printNodes prolog ++ '<' :: name ++ printAttrs attrs ++ ['>'] =
      printNodes prolog ++ '<' :: (name ++ (printAttrs attrs ++ ['>'])) := by
    simp [List.append_assoc]
  rw [e]
  have hnn := noCR_validName hname
  obtain ⟨c0, ds, hq, hc0, hds⟩ := hname
  subst hq
  rw [List.cons_append]
  apply parse_root_none prolog hpro c0 _ hc0
  have hds' : '\r' ∉ ds := fun m => hnn (List.mem_cons_of_mem _ m)
  rw [normEol_append_noCR _ _ hds',
    normEol_append_noCR _ _ (noCR_printAttrs attrs hattrs),
    normEol_cons_ne (by decide), normEol.eq_1]
  intro f hf
  cases f with
  | zero => omega
  | succ g =>
    have hlen : ds.length + (printAttrs attrs).length + 2 ≤ g := by
      have h := hf
      simp only [List.length_append, List.length_cons, List.length_nil] at h
      omega
    have hpv := printAttrs_length_ge_value attrs
    have hat : parseAttrs g [] (printAttrs attrs ++ ['>']) =
        some (attrs, [], false) := by
      have h := parseAttrs_print_open attrs [] [] g hattrs
        (by intro kv _ e; simp at e)
        (fun kv hkv => by have := hpv kv hkv; omega)
        (by have := printAttrs_length_ge attrs; omega)
      simpa using h
    have hpn : parseName (c0 :: (ds ++ (printAttrs attrs ++ ['>']))) =
        some (c0 :: ds, printAttrs attrs ++ ['>']) :=
      parseName_append (cs := c0 :: ds) ⟨c0, ds, rfl, hc0, hds⟩
        (printAttrs_head_not_name attrs _ (by
          intro c hc
          simp at hc
          rw [← hc]
          exact isNameChar_false_of not_nameChar_gt))
    apply parseElement_unclosed hpn hat
    intro ns r3 h
    cases g with
    | zero => cases h
    | succ g' =>
      have e2 : parseNodes (g' + 1) [] = some ([], []) := rfl
      rw [e2] at h
      cases h
      rfl

theorem rejects_second_root (d : Document) (c : Char) (rest : List Char)
    (hwf : WF d) (hc : IsNameStart c) :
    parse (print d ++ '<' :: c :: rest) = none := by
  have hcr : c ≠ '\r' := fun e => not_nameChar_cr (e ▸ IsNameStart.toNameChar hc)
  have hn : normEol (print d ++ '<' :: c :: rest) =
      print d ++ '<' :: c :: normEol rest := by
    rw [normEol_append_noCR _ _ (noCR_print d hwf), normEol_cons_ne (by decide),
      normEol_cons_ne hcr]
  show parseDocument ((normEol (print d ++ '<' :: c :: rest)).length + 1)
    (normEol (print d ++ '<' :: c :: rest)) = none
  rw [hn]
  generalize normEol rest = R
  obtain ⟨hpro, hroot, ⟨name, attrs, content, hreq⟩, hepi⟩ := hwf
  rw [hreq] at hroot
  have hroot2 := hroot
  cases hroot with
  | elem hname hattrs hcontent =>
    obtain ⟨c0, ds, hq0, hc0, hds⟩ := hname
    have hP : print d ++ '<' :: c :: R = printNodes d.prolog ++
        (printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R)) := by
      simp [print, List.append_assoc]
    rw [hP]
    have harg : printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R) =
        '<' :: c0 :: (ds ++ (printAttrs attrs ++
          (if content = [] then ['/', '>']
           else '>' :: (printNodes content ++ '<' :: '/' ::
             ((c0 :: ds) ++ ['>'])))) ++
          (printNodes d.epilog ++ '<' :: c :: R)) := by
      rw [hreq, hq0]
      simp [printNode, printElem, List.append_assoc, List.cons_append]
    have hstoproot : ∀ f, 1 ≤ f →
        parseMisc f (printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R)) =
          some ([], skipWs (printNode d.root ++
            (printNodes d.epilog ++ '<' :: c :: R))) := by
      intro f hf
      cases f with
      | zero => omega
      | succ f' =>
        rw [harg, skipWs_cons (show isWs '<' = false by decide)]
        exact parseMisc_stop hc0
    have hsw : skipWs (printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R)) =
        printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R) := by
      rw [harg]
      exact skipWs_cons (by decide)
    have hstopX : ∀ f, 1 ≤ f →
        parseMisc f ('<' :: c :: R) = some ([], skipWs ('<' :: c :: R)) := by
      intro f hf
      cases f with
      | zero => omega
      | succ f' =>
        rw [skipWs_cons (show isWs '<' = false by decide)]
        exact parseMisc_stop hc
    let F := (printNodes d.prolog ++
      (printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R))).length + 1
    have hpro' : parseMisc F (printNodes d.prolog ++
        (printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R))) =
        some (d.prolog, skipWs (printNode d.root ++
          (printNodes d.epilog ++ '<' :: c :: R))) :=
      parseMisc_print d.prolog _ hpro hstoproot _ (by
        simp only [F, List.length_append]; omega)
    have hroot' : parseElement F
        (printNode d.root ++ (printNodes d.epilog ++ '<' :: c :: R)) =
        some (d.root, printNodes d.epilog ++ '<' :: c :: R) := by
      rw [hreq]
      exact (elem_nodes (printNode (.elem name attrs content)).length).1
        _ (by
          have e2 : (printNode d.root).length =
              (printNode (.elem name attrs content)).length := by
            rw [hreq]
          simp only [F, List.length_append]; omega)
        name attrs content _ hroot2 rfl
    have hepi' : parseMisc F (printNodes d.epilog ++ '<' :: c :: R) =
        some (d.epilog, skipWs ('<' :: c :: R)) :=
      parseMisc_print d.epilog _ hepi hstopX F (by
        simp only [F, List.length_append, List.length_cons]; omega)
    have hX : skipWs ('<' :: c :: R) = '<' :: c :: R :=
      skipWs_cons (by decide)
    show parseDocument F _ = none
    simp only [parseDocument, hpro', hsw, hroot', hepi', hX]
    rfl

theorem rejects_xml_declaration (t rest : List Char) (ht : ValidName t)
    (hx : IsXmlTarget t) (hr : ∀ c, rest.head? = some c → ¬ IsNameChar c) :
    parse ('<' :: '?' :: t ++ rest) = none := by
  have hn : normEol ('<' :: '?' :: t ++ rest) = '<' :: '?' :: (t ++ normEol rest) := by
    rw [List.cons_append, List.cons_append, normEol_cons_ne (by decide),
      normEol_cons_ne (by decide), normEol_append_noCR _ _ (noCR_validName ht)]
  have hpi : parsePI (t ++ normEol rest) = none := by
    unfold parsePI
    rw [parseName_append ht (normEol_head_not_name rest hr)]
    split
    · rename_i target r1 heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj heq)
      have hx' : t.map Char.toLower = ['x', 'm', 'l'] := hx
      rw [ite_eq_left hx']
    · rename_i heq
      cases heq
  have hm : ∀ f, parseMisc f ('<' :: '?' :: (t ++ normEol rest)) = none := by
    intro f
    cases f with
    | zero => rfl
    | succ f => exact parseMisc_pi_none '<' '?' _ rfl rfl hpi f
  show parseDocument ((normEol ('<' :: '?' :: t ++ rest)).length + 1)
    (normEol ('<' :: '?' :: t ++ rest)) = none
  rw [hn]
  simp only [parseDocument, hm]

end Xml.Proofs
