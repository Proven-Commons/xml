/-
  The round trip proof: for every well formed document, parsing
  its printed form gives the document back.

  The statement proved here is `parse_print`; `Spec.parse_print`
  in `Spec.lean` states it, and `Proofs/SpecProofs.lean` proves
  that statement with this theorem.

  The proof goes layer by layer: references, text runs, attribute
  values, character data, names, comment bodies, processing
  instruction data, attributes, then elements and content together
  by a strong induction on the length of the printed form, then
  the prolog and epilog lists, and at last the document.
-/

import Xml

namespace Xml.Proofs

open Xml

set_option maxRecDepth 10000

/-! ## Small facts -/

theorem isWs_of_ne {c : Char} (h1 : c ≠ ' ') (h2 : c ≠ '\t')
    (h3 : c ≠ '\n') (h4 : c ≠ '\r') : isWs c = false := by
  simp [isWs, h1, h2, h3, h4]

theorem isWs_lt : isWs '<' = false := by decide
theorem isWs_slash : isWs '/' = false := by decide

/-- Skipping whitespace over a list whose head is not whitespace
    changes nothing. -/
theorem skipWs_cons {c : Char} {cs : List Char} (h : isWs c = false) :
    skipWs (c :: cs) = c :: cs := by
  simp [skipWs, h]

theorem isLegalChar_of {c : Char} (h : LegalChar c) : isLegalChar c = true :=
  isLegalChar_iff.mpr h

theorem isNameStart_of {c : Char} (h : IsNameStart c) : isNameStart c = true :=
  isNameStart_iff.mpr h

theorem isNameChar_of {c : Char} (h : IsNameChar c) : isNameChar c = true :=
  isNameChar_iff.mpr h

theorem isNameChar_false_of {c : Char} (h : ¬ IsNameChar c) :
    isNameChar c = false := by
  cases hb : isNameChar c with
  | true => exact absurd (isNameChar_iff.mp hb) h
  | false => rfl

/-- A name start character is a name character. -/
theorem IsNameStart.toNameChar {c : Char} (h : IsNameStart c) :
    IsNameChar c :=
  Or.inl h

/-- A name start character differs from any character that fails
    the name start test. -/
theorem IsNameStart.ne_of_test {c d : Char} (h : IsNameStart c)
    (hd : isNameStart d = false) : c ≠ d := by
  intro e
  subst e
  have hb : isNameStart c = true := isNameStart_of h
  rw [hb] at hd
  exact Bool.false_ne_true hd.symm

/-- A name start character is none of the marks that can follow a
    name in a printed tag. -/
theorem IsNameStart.ne_lt {c : Char} (h : IsNameStart c) : c ≠ '<' :=
  IsNameStart.ne_of_test h (by decide)

theorem IsNameStart.ne_bang {c : Char} (h : IsNameStart c) : c ≠ '!' :=
  IsNameStart.ne_of_test h (by decide)

theorem IsNameStart.ne_ws {c : Char} (h : IsNameStart c) : ¬ IsWs c := by
  intro hw
  rcases hw with e | e | e | e
  · exact IsNameStart.ne_of_test h (by decide) e
  · exact IsNameStart.ne_of_test h (by decide) e
  · exact IsNameStart.ne_of_test h (by decide) e
  · exact IsNameStart.ne_of_test h (by decide) e

/-- A character that fails the name character test is not a name
    character. -/
theorem not_nameChar_of_test {c : Char} (h : isNameChar c = false) :
    ¬ IsNameChar c := by
  intro hc
  have hb := isNameChar_iff.mpr hc
  rw [h] at hb
  exact Bool.false_ne_true hb

/-- The marks that follow a name in a printed tag are not name
    characters. -/
theorem not_nameChar_slash : ¬ IsNameChar '/' :=
  not_nameChar_of_test (by decide)
theorem not_nameChar_gt : ¬ IsNameChar '>' :=
  not_nameChar_of_test (by decide)
theorem not_nameChar_eq : ¬ IsNameChar '=' :=
  not_nameChar_of_test (by decide)
theorem not_nameChar_quest : ¬ IsNameChar '?' :=
  not_nameChar_of_test (by decide)
theorem not_nameChar_space : ¬ IsNameChar ' ' :=
  not_nameChar_of_test (by decide)

/-- The printed form of one character of character data: either
    an escape, whose head is an ampersand, or the character
    itself. -/
theorem escapeTextChar_head (c : Char) :
    (escapeTextChar c).head? = some '&' ∨ escapeTextChar c = [c] := by
  unfold escapeTextChar
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · exact Or.inr rfl

/-- An escaped character is never the empty list, and its head is
    never a greater sign. The second fact is what keeps `]]>` from
    ever forming in printed text: a greater sign only ever appears
    inside `&gt;`, behind an ampersand. -/
theorem escapeTextChar_ne_nil (c : Char) : escapeTextChar c ≠ [] := by
  intro he
  rcases escapeTextChar_head c with h | h
  · rw [he] at h
    simp at h
  · rw [he] at h
    simp at h

theorem escapeTextChar_head_ne_gt (c : Char) :
    (escapeTextChar c).head? ≠ some '>' := by
  rcases escapeTextChar_head c with h | h
  · rw [h]; decide
  · rw [h]
    intro hcon
    simp at hcon
    subst hcon
    have hgt : escapeTextChar '>' = ['&', 'g', 't', ';'] := by decide
    rw [hgt] at h
    simp at h

/-- An escaped attribute character is never the empty list, and
    its head is an ampersand when it is an escape. -/
theorem escapeAttrChar_head (c : Char) :
    (escapeAttrChar c).head? = some '&' ∨ escapeAttrChar c = [c] := by
  unfold escapeAttrChar
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · split
          · simp
          · split
            · simp
            · exact Or.inr rfl

theorem escapeAttrChar_ne_nil (c : Char) : escapeAttrChar c ≠ [] := by
  intro he
  rcases escapeAttrChar_head c with h | h
  · rw [he] at h
    simp at h
  · rw [he] at h
    simp at h

/-- The head of a printed text run followed by more text: the
    printed run of a nonempty list starts with the printed form of
    its first character. -/
theorem escapeText_head {c : Char} {cs : List Char} :
    (escapeText (c :: cs)).head? = (escapeTextChar c).head? := by
  have hne := escapeTextChar_ne_nil c
  simp only [escapeText, List.flatMap_cons]
  cases h : escapeTextChar c with
  | nil => exact absurd h hne
  | cons x xs => simp

theorem escapeText_length_ge (cs : List Char) :
    cs.length ≤ (escapeText cs).length := by
  induction cs with
  | nil => simp [escapeText]
  | cons c cs ih =>
    have h1 : 1 ≤ (escapeTextChar c).length := by
      cases h : escapeTextChar c with
      | nil => exact absurd h (escapeTextChar_ne_nil c)
      | cons x xs => simp
    have hlen : (escapeText (c :: cs)).length =
        (escapeTextChar c).length + (escapeText cs).length := by
      have e1 : escapeText (c :: cs) = escapeTextChar c ++ escapeText cs := rfl
      rw [e1, List.length_append]
    rw [List.length_cons, hlen]
    omega

theorem escapeAttr_length_ge (cs : List Char) :
    cs.length ≤ (escapeAttr cs).length := by
  induction cs with
  | nil => simp [escapeAttr]
  | cons c cs ih =>
    have h1 : 1 ≤ (escapeAttrChar c).length := by
      cases h : escapeAttrChar c with
      | nil => exact absurd h (escapeAttrChar_ne_nil c)
      | cons x xs => simp
    have hlen : (escapeAttr (c :: cs)).length =
        (escapeAttrChar c).length + (escapeAttr cs).length := by
      have e1 : escapeAttr (c :: cs) = escapeAttrChar c ++ escapeAttr cs := rfl
      rw [e1, List.length_append]
    rw [List.length_cons, hlen]
    omega

/-! ## References -/

theorem parseRef_lt {rest : List Char} :
    parseRef ('l' :: 't' :: ';' :: rest) = some ('<', rest) := rfl

theorem parseRef_gt {rest : List Char} :
    parseRef ('g' :: 't' :: ';' :: rest) = some ('>', rest) := rfl

theorem parseRef_amp {rest : List Char} :
    parseRef ('a' :: 'm' :: 'p' :: ';' :: rest) = some ('&', rest) := rfl

theorem parseRef_quot {rest : List Char} :
    parseRef ('q' :: 'u' :: 'o' :: 't' :: ';' :: rest) = some ('"', rest) := rfl

/-- A run of digits at the head of a text is read whole: when the
    text after the run does not start with a digit, the digit run
    reader stops at the end of the run. -/
theorem takeDigits_append {ds rest : List Char}
    (hd : ∀ d ∈ ds, isDigit d = true)
    (hr : ∀ c, rest.head? = some c → isDigit c = false) :
    takeDigits (ds ++ rest) = (ds, rest) := by
  induction ds generalizing rest with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r =>
      have hc : isDigit c = false := hr c rfl
      simp [takeDigits, hc]
  | cons d ds ih =>
    have hdd : isDigit d = true := hd d (by simp)
    have ih' := ih (fun x hx => hd x (List.mem_cons_of_mem d hx)) hr
    simp [takeDigits, hdd, ih']

theorem parseRef_dec13 {rest : List Char} :
    parseRef ('#' :: '1' :: '3' :: ';' :: rest) = some ('\r', rest) := by
  have htake : takeDigits ('1' :: '3' :: ';' :: rest) =
      (['1', '3'], ';' :: rest) := by
    show takeDigits (['1', '3'] ++ (';' :: rest)) = (['1', '3'], ';' :: rest)
    apply takeDigits_append
    · decide
    · intro c hc
      have hcc : c = ';' := (Option.some.inj hc).symm
      rw [hcc]
      decide
  have hval : digitsValue 10 (fun d => d.toNat - 48) ['1', '3'] = 13 := by
    decide
  have hchar : charRefChar 13 = some '\r' := by decide
  simp [parseRef, htake, hval, hchar]

theorem parseRef_dec9 {rest : List Char} :
    parseRef ('#' :: '9' :: ';' :: rest) = some ('\t', rest) := by
  have htake : takeDigits ('9' :: ';' :: rest) = (['9'], ';' :: rest) := by
    show takeDigits (['9'] ++ (';' :: rest)) = (['9'], ';' :: rest)
    apply takeDigits_append
    · decide
    · intro c hc
      have hcc : c = ';' := (Option.some.inj hc).symm
      rw [hcc]
      decide
  have hval : digitsValue 10 (fun d => d.toNat - 48) ['9'] = 9 := by decide
  have hchar : charRefChar 9 = some '\t' := by decide
  simp [parseRef, htake, hval, hchar]

theorem parseRef_dec10 {rest : List Char} :
    parseRef ('#' :: '1' :: '0' :: ';' :: rest) = some ('\n', rest) := by
  have htake : takeDigits ('1' :: '0' :: ';' :: rest) =
      (['1', '0'], ';' :: rest) := by
    show takeDigits (['1', '0'] ++ (';' :: rest)) = (['1', '0'], ';' :: rest)
    apply takeDigits_append
    · decide
    · intro c hc
      have hcc : c = ';' := (Option.some.inj hc).symm
      rw [hcc]
      decide
  have hval : digitsValue 10 (fun d => d.toNat - 48) ['1', '0'] = 10 := by
    decide
  have hchar : charRefChar 10 = some '\n' := by decide
  simp [parseRef, htake, hval, hchar]

/-! ## Text runs and attribute values -/

/-- The five shapes of a printed character of character data, with
    the character each shape comes from. -/
theorem escapeTextChar_cases (c : Char) :
    (c = '&' ∧ escapeTextChar c = ['&', 'a', 'm', 'p', ';']) ∨
    (c = '<' ∧ escapeTextChar c = ['&', 'l', 't', ';']) ∨
    (c = '>' ∧ escapeTextChar c = ['&', 'g', 't', ';']) ∨
    (c = '\r' ∧ escapeTextChar c = ['&', '#', '1', '3', ';']) ∨
    (c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '\r' ∧ escapeTextChar c = [c]) := by
  by_cases h1 : c = '&'
  · exact Or.inl ⟨h1, by simp [escapeTextChar, h1]⟩
  · by_cases h2 : c = '<'
    · exact Or.inr (Or.inl ⟨h2, by simp [escapeTextChar, h2]⟩)
    · by_cases h3 : c = '>'
      · exact Or.inr (Or.inr (Or.inl ⟨h3, by simp [escapeTextChar, h3]⟩))
      · by_cases h4 : c = '\r'
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl ⟨h4, by simp [escapeTextChar, h4]⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨h1, h2, h3, h4, by simp [escapeTextChar, h1, h2, h3, h4]⟩)))

/-- The seven shapes of a printed character of an attribute
    value. -/
theorem escapeAttrChar_cases (c : Char) :
    (c = '&' ∧ escapeAttrChar c = ['&', 'a', 'm', 'p', ';']) ∨
    (c = '<' ∧ escapeAttrChar c = ['&', 'l', 't', ';']) ∨
    (c = '"' ∧ escapeAttrChar c = ['&', 'q', 'u', 'o', 't', ';']) ∨
    (c = '\t' ∧ escapeAttrChar c = ['&', '#', '9', ';']) ∨
    (c = '\n' ∧ escapeAttrChar c = ['&', '#', '1', '0', ';']) ∨
    (c = '\r' ∧ escapeAttrChar c = ['&', '#', '1', '3', ';']) ∨
    (c ≠ '&' ∧ c ≠ '<' ∧ c ≠ '"' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\r' ∧
      escapeAttrChar c = [c]) := by
  by_cases h1 : c = '&'
  · exact Or.inl ⟨h1, by simp [escapeAttrChar, h1]⟩
  · by_cases h2 : c = '<'
    · exact Or.inr (Or.inl ⟨h2, by simp [escapeAttrChar, h2]⟩)
    · by_cases h3 : c = '"'
      · exact Or.inr (Or.inr (Or.inl ⟨h3, by simp [escapeAttrChar, h3]⟩))
      · by_cases h4 : c = '\t'
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl ⟨h4, by simp [escapeAttrChar, h4]⟩)))
        · by_cases h5 : c = '\n'
          · exact Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl ⟨h5, by simp [escapeAttrChar, h5]⟩))))
          · by_cases h6 : c = '\r'
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨h6, by simp [escapeAttrChar, h6]⟩)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨h1, h2, h3, h4, h5, h6,
                 by simp [escapeAttrChar, h1, h2, h3, h4, h5, h6]⟩)))))

/-- A printed text run followed by the end of the text or by a
    mark never holds the run `]]>` at the junction the text reader
    is about to step over: the two characters the reader looks at
    after a `]` it just read are never `]` and `>`. -/
theorem escapeText_not_bracketGt {cs : List Char} {rest : List Char}
    (hrest : rest = [] ∨ rest.head? = some '<') :
    ¬ ((escapeText cs ++ rest).head? = some ']' ∧
       ((escapeText cs ++ rest).tail).head? = some '>') := by
  intro hcon
  obtain ⟨h1, h2⟩ := hcon
  cases cs with
  | nil =>
    simp only [escapeText, List.flatMap_nil, List.nil_append] at h1
    rcases hrest with h | h
    · rw [h] at h1
      simp at h1
    · rw [h] at h1
      simp at h1
  | cons d ds =>
    have e1 : escapeText (d :: ds) ++ rest =
        escapeTextChar d ++ (escapeText ds ++ rest) := by
      have e0 : escapeText (d :: ds) = escapeTextChar d ++ escapeText ds := rfl
      rw [e0, List.append_assoc]
    rw [e1] at h1 h2
    rcases escapeTextChar_head d with hd | hd
    · have hh : (escapeTextChar d ++ (escapeText ds ++ rest)).head? =
          some '&' := by
        cases hdd : escapeTextChar d with
        | nil => exact absurd hdd (escapeTextChar_ne_nil d)
        | cons x xs =>
          have hx : x = '&' := by
            have h2' := hd
            rw [hdd] at h2'
            simp at h2'
            exact h2'
          simp [hx]
      rw [hh] at h1
      simp at h1
    · rw [hd] at h2
      simp only [List.cons_append, List.tail_cons, List.nil_append] at h2
      cases ds with
      | nil =>
        simp only [escapeText, List.flatMap_nil, List.nil_append] at h2
        rcases hrest with h | h
        · rw [h] at h2
          simp at h2
        · rw [h] at h2
          simp at h2
      | cons e es =>
        have hgt := escapeTextChar_head_ne_gt e
        have hh : (escapeText (e :: es) ++ rest).head? =
            (escapeTextChar e).head? := by
          have e2 : escapeText (e :: es) ++ rest =
              escapeTextChar e ++ (escapeText es ++ rest) := by
            have e0 : escapeText (e :: es) =
                escapeTextChar e ++ escapeText es := rfl
            rw [e0, List.append_assoc]
          rw [e2]
          cases hdd : escapeTextChar e with
          | nil => exact absurd hdd (escapeTextChar_ne_nil e)
          | cons x xs => simp
        rw [hh] at h2
        exact hgt h2

/-- Reading back a printed text run gives the run back, when the
    text after it is empty or starts with a less sign (so the
    reader stops there). -/
theorem parseTextRun_escapeText : ∀ (cs : List Char) (rest : List Char),
    (∀ c ∈ cs, LegalChar c) →
    (rest = [] ∨ rest.head? = some '<') →
    ∀ (f : Nat), cs.length + 1 ≤ f →
    parseTextRun f (escapeText cs ++ rest) = some (cs, rest) := by
  intro cs
  induction cs with
  | nil =>
    intro rest _ hrest f hf
    cases f with
    | zero => simp at hf
    | succ f' =>
      cases rest with
      | nil => simp [parseTextRun, escapeText]
      | cons c t =>
        have hc : c = '<' := by
          rcases hrest with h | h
          · simp at h
          · have h2 : (c :: t).head? = some c := rfl
            rw [h2] at h
            exact Option.some.inj h
        subst hc
        simp [parseTextRun, escapeText]
  | cons c cs ih =>
    intro rest hlegal hrest f hf
    have hlegal' : ∀ x ∈ cs, LegalChar x :=
      fun x hx => hlegal x (List.mem_cons_of_mem c hx)
    have hclegal : LegalChar c := hlegal c (by simp)
    cases f with
    | zero =>
      simp only [List.length_cons] at hf
      omega
    | succ f' =>
      have hf' : cs.length + 1 ≤ f' := by
        simp only [List.length_cons] at hf
        omega
      have ih' := ih rest hlegal' hrest f' hf'
      have e0 : escapeText (c :: cs) = escapeTextChar c ++ escapeText cs := rfl
      rw [e0, List.append_assoc]
      rcases escapeTextChar_cases c with
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseTextRun, ih', parseRef_amp]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseTextRun, ih', parseRef_lt]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseTextRun, ih', parseRef_gt]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseTextRun, ih', parseRef_dec13]
      · rw [h5]
        simp only [List.cons_append]
        by_cases hc : c = ']'
        · subst hc
          have hnb := escapeText_not_bracketGt (cs := cs) (rest := rest) hrest
          simp only [parseTextRun, List.nil_append]
          rw [ite_eq_left trivial, ite_eq_right hnb, ih']
          simp
        · simp [parseTextRun, ih', h1, h2, hc,
            isLegalChar_of hclegal]

/-- Reading back a printed attribute value gives the value back.
    The printer uses double quotes, so the quote here is the
    double quote. -/
theorem parseAttrValue_escapeAttr : ∀ (cs : List Char) (rest : List Char),
    (∀ c ∈ cs, LegalChar c) →
    ∀ (f : Nat), cs.length + 1 ≤ f →
    parseAttrValue '"' f (escapeAttr cs ++ '"' :: rest) = some (cs, rest) := by
  intro cs
  induction cs with
  | nil =>
    intro rest _ f hf
    cases f with
    | zero => simp at hf
    | succ f' => simp [parseAttrValue, escapeAttr]
  | cons c cs ih =>
    intro rest hlegal f hf
    have hlegal' : ∀ x ∈ cs, LegalChar x :=
      fun x hx => hlegal x (List.mem_cons_of_mem c hx)
    have hclegal : LegalChar c := hlegal c (by simp)
    cases f with
    | zero =>
      simp only [List.length_cons] at hf
      omega
    | succ f' =>
      have hf' : cs.length + 1 ≤ f' := by
        simp only [List.length_cons] at hf
        omega
      have ih' := ih rest hlegal' f' hf'
      have e0 : escapeAttr (c :: cs) = escapeAttrChar c ++ escapeAttr cs := rfl
      rw [e0, List.append_assoc]
      rcases escapeAttrChar_cases c with
        ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2, h3, h4, h5, h6, h7⟩
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', parseRef_amp]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', parseRef_lt]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', parseRef_quot]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', parseRef_dec9]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', parseRef_dec10]
      · subst h1
        rw [h2]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', parseRef_dec13]
      · rw [h7]
        simp only [List.cons_append]
        simp [parseAttrValue, ih', h1, h2, h3, h4, h5, h6,
          isLegalChar_of hclegal]

/-- Reading back printed character data gives the data back, when
    the reader stops at the text that follows. -/
theorem parseCharData_escapeText (cs : List Char) (rest : List Char)
    (hne : cs ≠ [])
    (hlegal : ∀ c ∈ cs, LegalChar c)
    (hrest : rest = [] ∨ rest.head? = some '<')
    (hstop : ∀ f, 1 ≤ f → parseCharData f rest = some ([], rest))
    (f : Nat) (hf : cs.length + 2 ≤ f) :
    parseCharData f (escapeText cs ++ rest) = some (cs, rest) := by
  cases f with
  | zero => omega
  | succ f' =>
    have hf1 : cs.length + 1 ≤ f' := by omega
    have htr := parseTextRun_escapeText cs rest hlegal hrest f' hf1
    have hst := hstop f' (by
      have h1 : 1 ≤ cs.length := by
        cases cs with
        | nil => exact absurd rfl hne
        | cons c cs' => simp
      omega)
    obtain ⟨c, cs', hcs⟩ : ∃ c cs', cs = c :: cs' := by
      cases cs with
      | nil => exact absurd rfl hne
      | cons c cs' => exact ⟨c, cs', rfl⟩
    subst hcs
    have e0 : escapeText (c :: cs') = escapeTextChar c ++ escapeText cs' := rfl
    rw [e0, List.append_assoc]
    rcases escapeTextChar_cases c with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
    · subst h1
      rw [h2]
      simp only [List.cons_append]
      have htr2 : parseTextRun f'
          ('&' :: 'a' :: 'm' :: 'p' :: ';' :: (escapeText cs' ++ rest)) =
          some ('&' :: cs', rest) := htr
      simp [parseCharData, htr2, hst]
    · subst h1
      rw [h2]
      simp only [List.cons_append]
      have htr2 : parseTextRun f'
          ('&' :: 'l' :: 't' :: ';' :: (escapeText cs' ++ rest)) =
          some ('<' :: cs', rest) := htr
      simp [parseCharData, htr2, hst]
    · subst h1
      rw [h2]
      simp only [List.cons_append]
      have htr2 : parseTextRun f'
          ('&' :: 'g' :: 't' :: ';' :: (escapeText cs' ++ rest)) =
          some ('>' :: cs', rest) := htr
      simp [parseCharData, htr2, hst]
    · subst h1
      rw [h2]
      simp only [List.cons_append]
      have htr2 : parseTextRun f'
          ('&' :: '#' :: '1' :: '3' :: ';' :: (escapeText cs' ++ rest)) =
          some ('\r' :: cs', rest) := htr
      simp [parseCharData, htr2, hst]
    · rw [h5]
      simp only [List.cons_append]
      have htr2 : parseTextRun f' (c :: (escapeText cs' ++ rest)) =
          some (c :: cs', rest) := by
        have htr' := htr
        rw [e0, h5] at htr'
        simpa only [List.cons_append, List.append_assoc, List.nil_append]
          using htr'
      simp [parseCharData, htr2, hst, h2]

/-! ## Names -/

theorem takeNameChars_append {ds rest : List Char}
    (hd : ∀ d ∈ ds, isNameChar d = true)
    (hr : ∀ c, rest.head? = some c → isNameChar c = false) :
    takeNameChars (ds ++ rest) = (ds, rest) := by
  induction ds generalizing rest with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c r =>
      have hc : isNameChar c = false := hr c rfl
      simp [takeNameChars, hc]
  | cons d ds ih =>
    have hdd : isNameChar d = true := hd d (by simp)
    have ih' := ih (fun x hx => hd x (List.mem_cons_of_mem d hx)) hr
    simp [takeNameChars, hdd, ih']

/-- A valid name at the head of a text is read whole, when the text
    after it does not start with a name character. -/
theorem parseName_append {cs rest : List Char} (hv : ValidName cs)
    (hr : ∀ c, rest.head? = some c → isNameChar c = false) :
    parseName (cs ++ rest) = some (cs, rest) := by
  obtain ⟨c, ds, hcs, hstart, hchars⟩ := hv
  subst hcs
  have hsc : isNameStart c = true := isNameStart_of hstart
  have htake := takeNameChars_append (ds := ds) (rest := rest)
    (fun d hd => isNameChar_of (hchars d hd)) hr
  simp [parseName, hsc, htake]


/-! ## Comments and processing instructions -/

/-- One step of the comment body reader over a dash that does not
    close the comment. -/
theorem parseCommentBody_dash_cons {d : Char} {xs : List Char}
    (hd : d ≠ '-') :
    parseCommentBody ('-' :: d :: xs) =
      (parseCommentBody (d :: xs)).map fun (b, r) => ('-' :: b, r) := by
  simp [parseCommentBody, hd]

/-- Reading back a printed comment body gives the body back. -/
theorem parseCommentBody_print : ∀ (cs : List Char) (rest : List Char),
    NoDashDash cs → NotDashEnd cs → (∀ c ∈ cs, LegalChar c) →
    parseCommentBody (cs ++ '-' :: '-' :: '>' :: rest) = some (cs, rest) := by
  intro cs
  induction cs with
  | nil =>
    intro rest _ _ _
    simp [parseCommentBody]
  | cons c cs ih =>
    intro rest hdd hde hlegal
    have hlegal' : ∀ x ∈ cs, LegalChar x :=
      fun x hx => hlegal x (List.mem_cons_of_mem c hx)
    have hclegal : LegalChar c := hlegal c (by simp)
    have hdd' : NoDashDash cs := by
      intro pre suf h
      exact hdd (c :: pre) suf (by simp [h])
    have hde' : NotDashEnd cs := by
      intro pre h
      exact hde (c :: pre) (by simp [h])
    have ih' := ih rest hdd' hde' hlegal'
    by_cases hc : c = '-'
    · subst hc
      cases cs with
      | nil =>
        exfalso
        exact hde [] (by simp)
      | cons d ds =>
        have hd : d ≠ '-' := by
          intro e
          subst e
          exact hdd [] ds (by simp)
        have e1 : ('-' :: d :: ds) ++ '-' :: '-' :: '>' :: rest =
            '-' :: d :: (ds ++ '-' :: '-' :: '>' :: rest) := by
          simp
        rw [e1, parseCommentBody_dash_cons hd]
        have ih2 : parseCommentBody (d :: (ds ++ '-' :: '-' :: '>' :: rest)) =
            some (d :: ds, rest) := by
          have := ih'
          rwa [show (d :: ds) ++ '-' :: '-' :: '>' :: rest =
            d :: (ds ++ '-' :: '-' :: '>' :: rest) by simp] at this
        rw [ih2]
        rfl
    · have e1 : (c :: cs) ++ '-' :: '-' :: '>' :: rest =
          c :: (cs ++ '-' :: '-' :: '>' :: rest) := rfl
      rw [e1]
      simp [parseCommentBody, ih', hc, isLegalChar_of hclegal]

/-- One step of the processing instruction data reader over a
    question mark that does not close the instruction. -/
theorem parsePIData_quest_cons {d : Char} {xs : List Char}
    (hd : d ≠ '>') :
    parsePIData ('?' :: d :: xs) =
      (parsePIData (d :: xs)).map fun (b, r) => ('?' :: b, r) := by
  simp [parsePIData, hd]

/-- Reading back printed processing instruction data gives the
    data back. -/
theorem parsePIData_print : ∀ (d : List Char) (rest : List Char),
    NoQClose d → (∀ c ∈ d, LegalChar c) →
    parsePIData (d ++ '?' :: '>' :: rest) = some (d, rest) := by
  intro d
  induction d with
  | nil =>
    intro rest _ _
    simp [parsePIData]
  | cons c d ih =>
    intro rest hq hlegal
    have hlegal' : ∀ x ∈ d, LegalChar x :=
      fun x hx => hlegal x (List.mem_cons_of_mem c hx)
    have hclegal : LegalChar c := hlegal c (by simp)
    have hq' : NoQClose d := by
      intro pre suf h
      exact hq (c :: pre) suf (by simp [h])
    have ih' := ih rest hq' hlegal'
    by_cases hc : c = '?'
    · subst hc
      cases d with
      | nil =>
        simp [parsePIData]
      | cons e es =>
        have he : e ≠ '>' := by
          intro hgt
          subst hgt
          exact hq [] es (by simp)
        have e1 : ('?' :: e :: es) ++ '?' :: '>' :: rest =
            '?' :: e :: (es ++ '?' :: '>' :: rest) := by
          simp
        rw [e1, parsePIData_quest_cons he]
        have ih2 : parsePIData (e :: (es ++ '?' :: '>' :: rest)) =
            some (e :: es, rest) := ih'
        rw [ih2]
        rfl
    · have e1 : (c :: d) ++ '?' :: '>' :: rest =
          c :: (d ++ '?' :: '>' :: rest) := rfl
      rw [e1]
      simp [parsePIData, ih', hc, isLegalChar_of hclegal]

/-- Whitespace, as the test the parser runs, is false of a
    character that is no whitespace character. -/
theorem isWs_false_of_not {c : Char} (h : ¬ IsWs c) : isWs c = false := by
  have h1 : c ≠ ' ' := fun e => h (Or.inl e)
  have h2 : c ≠ '\t' := fun e => h (Or.inr (Or.inl e))
  have h3 : c ≠ '\n' := fun e => h (Or.inr (Or.inr (Or.inl e)))
  have h4 : c ≠ '\r' := fun e => h (Or.inr (Or.inr (Or.inr e)))
  exact isWs_of_ne h1 h2 h3 h4

/-- One step of the processing instruction reader, when the target
    is followed by a space: the data reader runs after the
    whitespace. Proved by splitting the reader's match rather than
    by `simp`, which keeps the proof term small for every kernel. -/
theorem parsePI_space {cs t X : List Char}
    (hpn : parseName cs = some (t, ' ' :: X))
    (hres : ¬ (t.map Char.toLower = ['x', 'm', 'l'])) :
    parsePI cs =
      (parsePIData (skipWs (' ' :: X))).map (fun p => (Node.pi t p.1, p.2)) := by
  rw [parsePI, hpn]
  split
  · rename_i target r1 e
    cases e
    rw [ite_eq_right hres]
    split
    · rename_i r2 e
      exact absurd (List.cons.inj e).1 (by decide)
    · rename_i c tl e
      cases e
      rw [ite_eq_left (show isWs ' ' = true by decide)]
      cases parsePIData (skipWs (' ' :: X)) with
      | none => rfl
      | some p => rfl
    · rename_i e
      cases e
  · rename_i e
    cases e

/-- Reading back a printed processing instruction gives the
    instruction back. The input is the text after `<?`, exactly as
    `parsePI` receives it. -/
theorem parsePI_print (t d : List Char) (rest : List Char)
    (hname : ValidName t) (hres : ¬ IsXmlTarget t)
    (hq : NoQClose d) (hlegal : ∀ c ∈ d, LegalChar c)
    (hstart : d = [] ∨ ∀ c cs, d = c :: cs → ¬ IsWs c) :
    parsePI (t ++ (if d = [] then ['?', '>'] else ' ' :: d ++ ['?', '>']) ++
        rest) =
      some (.pi t d, rest) := by
  have hres' : ¬ (t.map Char.toLower = ['x', 'm', 'l']) := hres
  cases hd : d with
  | nil =>
    subst hd
    have hpn := parseName_append hname (rest := ['?', '>'] ++ rest) (by
      intro c hc
      simp at hc
      rw [← hc]
      exact isNameChar_false_of not_nameChar_quest)
    rw [ite_eq_left rfl, List.append_assoc]
    simp only [parsePI]
    rw [hpn]
    simp [hres']
  | cons c0 d0 =>
    subst hd
    have hpn := parseName_append hname
      (rest := (' ' :: (c0 :: d0) ++ ['?', '>']) ++ rest) (by
      intro c hc
      simp at hc
      rw [← hc]
      exact isNameChar_false_of not_nameChar_space)
    have hstart' : ¬ IsWs c0 := by
      rcases hstart with h | h
      · simp at h
      · exact h c0 d0 rfl
    have hsk : skipWs ((' ' :: (c0 :: d0) ++ ['?', '>']) ++ rest) =
        (c0 :: d0) ++ '?' :: '>' :: rest := by
      have e1 : (' ' :: (c0 :: d0) ++ ['?', '>']) ++ rest =
          ' ' :: ((c0 :: d0) ++ '?' :: '>' :: rest) := by
        simp [List.append_assoc]
      rw [e1]
      have hw : isWs ' ' = true := by decide
      have hc0 : isWs c0 = false := isWs_false_of_not hstart'
      simp [skipWs, hw, hc0]
    have hpd := parsePIData_print (c0 :: d0) rest hq hlegal
    rw [ite_eq_right (by simp), List.append_assoc]
    have e1 : (' ' :: (c0 :: d0) ++ ['?', '>']) ++ rest =
        ' ' :: ((c0 :: d0) ++ '?' :: '>' :: rest) := by
      simp [List.append_assoc]
    rw [e1] at hpn hsk
    rw [e1, parsePI_space hpn hres', hsk, hpd]
    rfl

/-! ## Printed lengths -/

/-- The printed attribute list is at least as long as the list of
    attributes. -/
theorem printAttrs_length_ge : ∀ (attrs : List (List Char × List Char)),
    attrs.length ≤ (printAttrs attrs).length := by
  intro attrs
  induction attrs with
  | nil => simp [printAttrs]
  | cons kv rest ih =>
    have h2 := escapeAttr_length_ge kv.2
    simp only [printAttrs, List.length_append, List.length_cons]
    omega

/-- The printed attribute list is long enough to cover any one
    value in it, plus one character per attribute. -/
theorem printAttrs_length_ge_value :
    ∀ (attrs : List (List Char × List Char)) (kv : List Char × List Char),
    kv ∈ attrs → kv.2.length + attrs.length ≤ (printAttrs attrs).length := by
  intro attrs
  induction attrs with
  | nil => intro kv h; simp at h
  | cons kv0 rest ih =>
    intro kv h
    have h3 := printAttrs_length_ge rest
    rcases List.mem_cons.mp h with rfl | h'
    · have h2 := escapeAttr_length_ge kv.2
      simp only [printAttrs, List.length_append, List.length_cons]
      omega
    · have h4 := ih kv h'
      have h2 := escapeAttr_length_ge kv0.2
      simp only [printAttrs, List.length_append, List.length_cons]
      omega

/-! ## Stopping character data -/

/-- Character data stops at a less sign whose next character is
    not the bang that would open a CDATA section. -/
theorem parseCharData_stop_lt_cons {c : Char} {r : List Char}
    (hc : c ≠ '!') :
    ∀ f, 1 ≤ f →
    parseCharData f ('<' :: c :: r) = some ([], '<' :: c :: r) := by
  intro f hf
  cases f with
  | zero => simp at hf
  | succ f' => simp [parseCharData, hc]

/-- Character data stops at a less sign at the end of the text. -/
theorem parseCharData_stop_lt_nil :
    ∀ f, 1 ≤ f → parseCharData f ['<'] = some ([], ['<']) := by
  intro f hf
  cases f with
  | zero => simp at hf
  | succ f' => simp [parseCharData]

/-- Character data stops at the marks that open a comment. -/
theorem parseCharData_stop_comment {r : List Char} :
    ∀ f, 1 ≤ f →
    parseCharData f ('<' :: '!' :: '-' :: '-' :: r) =
      some ([], '<' :: '!' :: '-' :: '-' :: r) := by
  intro f hf
  cases f with
  | zero => simp at hf
  | succ f' => simp [parseCharData]

/-! ## Attributes -/

/-- Reading back a printed attribute list gives the attributes
    back, on top of the ones already read. The end of the tag is
    left to the caller: the statement ends in a hypothesis that
    says what the reader does at the text that follows the printed
    attributes. -/
theorem parseAttrs_print : ∀ (attrs : List (List Char × List Char))
    (acc : List (List Char × List Char)) (tail : List Char) (f : Nat)
    (res : Option (List (List Char × List Char) × List Char × Bool)),
    AttrsOk attrs →
    (∀ kv ∈ attrs, ¬ acc.any (fun p => p.1 = kv.1)) →
    (∀ kv ∈ attrs, kv.2.length + attrs.length + 2 ≤ f) →
    attrs.length + 1 ≤ f →
    (∀ f', 1 ≤ f' → parseAttrs f' (acc ++ attrs) tail = res) →
    parseAttrs f acc (printAttrs attrs ++ tail) = res := by
  intro attrs
  induction attrs with
  | nil =>
    intro acc tail f res _ _ _ hf hfin
    have h1 : parseAttrs f (acc ++ []) tail = res := hfin f (by
      cases f with
      | zero => simp at hf
      | succ f' => omega)
    simpa [printAttrs] using h1
  | cons kv attrs ih =>
    intro acc tail f res hok hdisj hfv hf hfin
    obtain ⟨a, v⟩ := kv
    have hname : ValidName a := hok.1
    have hnx : a ≠ xmlnsName := hok.2.1
    have hval : ∀ c ∈ v, LegalChar c := hok.2.2.1
    have hnodup : ∀ kv2 ∈ attrs, kv2.1 ≠ a := hok.2.2.2.1
    have hok' : AttrsOk attrs := hok.2.2.2.2
    obtain ⟨c0, ds, ha, hc0, hds⟩ := hname
    subst ha
    cases f with
    | zero =>
      simp only [List.length_cons] at hf
      omega
    | succ f' =>
      have hf' : attrs.length + 1 ≤ f' := by
        simp only [List.length_cons] at hf
        omega
      have hfv' : ∀ kv2 ∈ attrs, kv2.2.length + attrs.length + 2 ≤ f' := by
        intro kv2 h2
        have h3 := hfv kv2 (List.mem_cons_of_mem _ h2)
        simp only [List.length_cons] at h3
        omega
      have hdisj' : ∀ kv2 ∈ attrs,
          ¬ (acc ++ [((c0 :: ds), v)]).any (fun p => p.1 = kv2.1) := by
        intro kv2 h2
        rw [List.any_append]
        simp only [List.any_cons, List.any_nil, Bool.or_eq_true,
          Bool.or_false]
        intro e
        rcases e with e | e
        · exact hdisj kv2 (List.mem_cons_of_mem _ h2) e
        · exact hnodup kv2 h2 (of_decide_eq_true e).symm
      have hfin' : ∀ f'', 1 ≤ f'' →
          parseAttrs f'' ((acc ++ [((c0 :: ds), v)]) ++ attrs) tail = res := by
        intro f'' hf''
        have h3 := hfin f'' hf''
        have e : (acc ++ [((c0 :: ds), v)]) ++ attrs =
            acc ++ (((c0 :: ds), v) :: attrs) := by
          simp [List.append_assoc]
        rwa [← e] at h3
      have ih' := ih (acc ++ [((c0 :: ds), v)]) tail f' res hok' hdisj'
        hfv' hf' hfin'
      have hsk : skipWs (printAttrs (((c0 :: ds), v) :: attrs) ++ tail) =
          (c0 :: ds) ++
            ('=' :: '"' :: escapeAttr v ++ '"' :: (printAttrs attrs ++ tail)) := by
        have hws1 : isWs ' ' = true := by decide
        have hws2 : isWs c0 = false :=
          isWs_false_of_not (IsNameStart.ne_ws hc0)
        simp [printAttrs, skipWs, hws1, hws2, List.append_assoc]
      have hpn : parseName
          ((c0 :: ds) ++
            ('=' :: '"' :: escapeAttr v ++ '"' :: (printAttrs attrs ++ tail))) =
          some ((c0 :: ds),
            '=' :: '"' :: escapeAttr v ++ '"' :: (printAttrs attrs ++ tail)) :=
        parseName_append ⟨c0, ds, rfl, hc0, hds⟩ (by
          intro c hc
          simp only [List.head?] at hc
          rw [← Option.some.inj hc]
          exact isNameChar_false_of not_nameChar_eq)
      have hpn2 : parseName
          (c0 :: (ds ++
            ('=' :: '"' :: (escapeAttr v ++ '"' :: (printAttrs attrs ++ tail))))) =
          some ((c0 :: ds),
            '=' :: '"' :: (escapeAttr v ++ '"' :: (printAttrs attrs ++ tail))) :=
        hpn
      have hval' : parseAttrValue '"' f'
          (escapeAttr v ++ '"' :: (printAttrs attrs ++ tail)) =
          some (v, printAttrs attrs ++ tail) :=
        parseAttrValue_escapeAttr v (printAttrs attrs ++ tail) hval f' (by
          have h3 := hfv ((c0 :: ds), v) (by simp)
          simp only [List.length_cons] at h3
          omega)
      have hdup : acc.any (fun p => p.1 = (c0 :: ds)) = false := by
        have h3 := hdisj ((c0 :: ds), v) (by simp)
        cases h4 : acc.any (fun p => p.1 = (c0 :: ds)) with
        | false => rfl
        | true => exact absurd h4 (by exact h3)
      have hc0ne1 : c0 ≠ '/' := by
        intro e
        subst e
        have h5 : isNameStart '/' = true := isNameStart_of hc0
        have h6 : isNameStart '/' = false := by decide
        rw [h6] at h5
        exact Bool.false_ne_true h5
      have hc0ne2 : c0 ≠ '>' := by
        intro e
        subst e
        have h5 : isNameStart '>' = true := isNameStart_of hc0
        have h6 : isNameStart '>' = false := by decide
        rw [h6] at h5
        exact Bool.false_ne_true h5
      have hstep : parseAttrs (f' + 1) acc
          (printAttrs (((c0 :: ds), v) :: attrs) ++ tail) =
          parseAttrs f' (acc ++ [((c0 :: ds), v)])
            (printAttrs attrs ++ tail) := by
        have hsw : startsWithWs
            (printAttrs (((c0 :: ds), v) :: attrs) ++ tail) = true := by
          simp [printAttrs, startsWithWs, isWs]
        simp [parseAttrs, hsk, hpn2, hval', hdup, hc0ne1, hnx,
          isNameStart_of hc0, hsw, List.cons_append,
          skipWs_cons (by decide : isWs '=' = false),
          skipWs_cons (by decide : isWs '"' = false)]
      rwa [hstep]

/-- Reading back a printed attribute list that ends a short form
    tag. -/
theorem parseAttrs_print_closed
    (attrs : List (List Char × List Char))
    (acc : List (List Char × List Char)) (rest : List Char) (f : Nat)
    (hok : AttrsOk attrs)
    (hdisj : ∀ kv ∈ attrs, ¬ acc.any (fun p => p.1 = kv.1))
    (hfv : ∀ kv ∈ attrs, kv.2.length + attrs.length + 2 ≤ f)
    (hf : attrs.length + 1 ≤ f) :
    parseAttrs f acc (printAttrs attrs ++ '/' :: '>' :: rest) =
      some (acc ++ attrs, rest, true) := by
  apply parseAttrs_print attrs acc _ f _ hok hdisj hfv hf
  intro f' hf'
  cases f' with
  | zero => simp at hf'
  | succ f'' =>
    simp [parseAttrs, skipWs, isWs_slash]

/-- Reading back a printed attribute list that ends a start tag. -/
theorem parseAttrs_print_open
    (attrs : List (List Char × List Char))
    (acc : List (List Char × List Char)) (rest : List Char) (f : Nat)
    (hok : AttrsOk attrs)
    (hdisj : ∀ kv ∈ attrs, ¬ acc.any (fun p => p.1 = kv.1))
    (hfv : ∀ kv ∈ attrs, kv.2.length + attrs.length + 2 ≤ f)
    (hf : attrs.length + 1 ≤ f) :
    parseAttrs f acc (printAttrs attrs ++ '>' :: rest) =
      some (acc ++ attrs, rest, false) := by
  apply parseAttrs_print attrs acc _ f _ hok hdisj hfv hf
  intro f' hf'
  cases f' with
  | zero => simp at hf'
  | succ f'' => rfl

/-! ## Elements and content -/

/-- The element half of the round trip, at a bound on the length
    of the printed element. -/
abbrev ElemProp (n : Nat) : Prop :=
  ∀ (f : Nat), n + 1 ≤ f → ∀ (name : List Char)
    (attrs : List (List Char × List Char)) (content : List Node)
    (rest : List Char),
    WFNode (.elem name attrs content) →
    (printNode (.elem name attrs content)).length = n →
    parseElement f (printNode (.elem name attrs content) ++ rest) =
      some (.elem name attrs content, rest)

/-- The content half of the round trip, at a bound two more than
    the length of the printed content: the two end tag characters
    that follow the content are part of the bound, which is what
    makes the bound drop at an element inside the content. -/
abbrev NodesProp (n : Nat) : Prop :=
  ∀ (f : Nat), n + 1 ≤ f → ∀ (nodes : List Node) (rest : List Char),
    WFNodes nodes →
    (printNodes nodes).length + 2 = n →
    parseNodes f (printNodes nodes ++ '<' :: '/' :: rest) =
      some (nodes, '<' :: '/' :: rest)

/-- A name head is not any of the characters that would send the
    content reader down another arm. -/
theorem IsNameStart.ne_slash {c : Char} (h : IsNameStart c) : c ≠ '/' := by
  intro e
  subst e
  have h5 : isNameStart '/' = true := isNameStart_of h
  have h6 : isNameStart '/' = false := by decide
  rw [h6] at h5
  exact Bool.false_ne_true h5

theorem IsNameStart.ne_quest {c : Char} (h : IsNameStart c) : c ≠ '?' := by
  intro e
  subst e
  have h5 : isNameStart '?' = true := isNameStart_of h
  have h6 : isNameStart '?' = false := by decide
  rw [h6] at h5
  exact Bool.false_ne_true h5

/-- The two halves together, by strong induction on the bound. -/
theorem elem_nodes : ∀ n, ElemProp n ∧ NodesProp n := by
  have aux : ∀ k, ∀ n, n ≤ k → ElemProp n ∧ NodesProp n := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have hn0 : n = 0 := by omega
      subst hn0
      constructor
      · intro f hf name attrs content rest hwf hlen
        simp [printNode, printElem] at hlen
      · intro f hf nodes rest hwf hlen
        omega
    | succ k ihk =>
      intro n hn
      by_cases hn2 : n ≤ k
      · exact ihk n hn2
      · have ih : ∀ m, m < n → ElemProp m ∧ NodesProp m :=
          fun m hm => ihk m (by omega)
        constructor
        · -- elements
          intro f hf name attrs content rest hwf hlen
          cases f with
          | zero => simp at hf
          | succ f' =>
            have hname : ValidName name := match hwf with
              | .elem a _ _ => a
            have hattrs : AttrsOk attrs := match hwf with
              | .elem _ a _ => a
            have hcontent : WFNodes content := match hwf with
              | .elem _ _ a => a
            obtain ⟨c0, ds, hnameq, hc0, hds⟩ := hname
            subst hnameq
            have hple : (printAttrs attrs).length + 4 ≤
                (printNode (.elem (c0 :: ds) attrs content)).length := by
              by_cases hc : content = []
              · subst hc
                simp [printNode, printElem, List.length_append]
              · simp [printNode, printElem, hc, List.length_append]
                omega
            have hfv : ∀ kv ∈ attrs, kv.2.length + attrs.length + 2 ≤ f' := by
              intro kv hkv
              have h1 := printAttrs_length_ge_value attrs kv hkv
              omega
            have hfattrs : attrs.length + 1 ≤ f' := by
              have h1 := printAttrs_length_ge attrs
              omega
            by_cases hc : content = []
            · subst hc
              have hpn : parseName
                  ((c0 :: ds) ++ (printAttrs attrs ++ '/' :: '>' :: rest)) =
                  some ((c0 :: ds), printAttrs attrs ++ '/' :: '>' :: rest) :=
                parseName_append ⟨c0, ds, rfl, hc0, hds⟩ (by
                  intro c hc
                  have hc2 : ∀ x, (printAttrs attrs ++ '/' :: '>' :: rest).head? =
                      some x → isNameChar x = false := by
                    intro x hx
                    cases attrs with
                    | nil =>
                      simp only [printAttrs, List.nil_append,
                        List.head?_cons] at hx
                      rw [← Option.some.inj hx]
                      exact isNameChar_false_of not_nameChar_slash
                    | cons kv as =>
                      simp only [printAttrs, List.cons_append,
                        List.head?_cons] at hx
                      rw [← Option.some.inj hx]
                      exact isNameChar_false_of not_nameChar_space
                  exact hc2 c hc)
              have hpn2 : parseName
                  (c0 :: (ds ++ (printAttrs attrs ++ '/' :: '>' :: rest))) =
                  some ((c0 :: ds), printAttrs attrs ++ '/' :: '>' :: rest) :=
                hpn
              have hat : parseAttrs f' [] (printAttrs attrs ++ '/' :: '>' :: rest) =
                  some (attrs, rest, true) := by
                have h := parseAttrs_print_closed attrs [] rest f' hattrs
                  (by intro kv _ e; simp at e) hfv hfattrs
                simpa using h
              simp [parseElement, printNode, printElem, hpn2, hat,
                List.append_assoc]
            · have hpn : parseName
                  ((c0 :: ds) ++ (printAttrs attrs ++
                    ('>' :: (printNodes content ++
                      '<' :: '/' :: ((c0 :: ds) ++ '>' :: rest))))) =
                  some ((c0 :: ds), printAttrs attrs ++
                    ('>' :: (printNodes content ++
                      '<' :: '/' :: ((c0 :: ds) ++ '>' :: rest)))) :=
                parseName_append ⟨c0, ds, rfl, hc0, hds⟩ (by
                  intro c hc
                  have hc2 : ∀ x, (printAttrs attrs ++
                      ('>' :: (printNodes content ++
                        '<' :: '/' :: ((c0 :: ds) ++ '>' :: rest)))).head? =
                      some x → isNameChar x = false := by
                    intro x hx
                    cases attrs with
                    | nil =>
                      simp only [printAttrs, List.nil_append,
                        List.head?_cons] at hx
                      rw [← Option.some.inj hx]
                      exact isNameChar_false_of not_nameChar_gt
                    | cons kv as =>
                      simp only [printAttrs, List.cons_append,
                        List.head?_cons] at hx
                      rw [← Option.some.inj hx]
                      exact isNameChar_false_of not_nameChar_space
                  exact hc2 c hc)
              have hpn2 : parseName
                  (c0 :: (ds ++ (printAttrs attrs ++
                    ('>' :: (printNodes content ++
                      '<' :: '/' :: c0 :: (ds ++ '>' :: rest)))))) =
                  some ((c0 :: ds), printAttrs attrs ++
                    ('>' :: (printNodes content ++
                      '<' :: '/' :: c0 :: (ds ++ '>' :: rest)))) :=
                hpn
              have hat : parseAttrs f' []
                  (printAttrs attrs ++
                    ('>' :: (printNodes content ++
                      '<' :: '/' :: c0 :: (ds ++ '>' :: rest)))) =
                  some (attrs, printNodes content ++
                    '<' :: '/' :: c0 :: (ds ++ '>' :: rest), false) := by
                have h := parseAttrs_print_open attrs []
                  (printNodes content ++ '<' :: '/' :: c0 :: (ds ++ '>' :: rest))
                  f' hattrs (by intro kv _ e; simp at e) hfv hfattrs
                simpa using h
              have hm : (printNodes content).length + 2 < n := by
                have hlb : (printNodes content).length + 3 ≤
                    (printNode (.elem (c0 :: ds) attrs content)).length := by
                  simp [printNode, printElem, hc, List.length_append]
                  omega
                omega
              have hnodes : parseNodes f'
                  (printNodes content ++ '<' :: '/' :: c0 :: (ds ++ '>' :: rest)) =
                  some (content, '<' :: '/' :: c0 :: (ds ++ '>' :: rest)) :=
                (ih ((printNodes content).length + 2) hm).2 f' (by omega)
                  content (c0 :: (ds ++ '>' :: rest)) hcontent rfl
              have hend2 : parseName (c0 :: (ds ++ '>' :: rest)) =
                  some ((c0 :: ds), '>' :: rest) :=
                parseName_append ⟨c0, ds, rfl, hc0, hds⟩ (by
                  intro c hc
                  simp only [List.head?_cons] at hc
                  rw [← Option.some.inj hc]
                  exact isNameChar_false_of not_nameChar_gt)
              have hend : parseName ((c0 :: ds) ++ '>' :: rest) =
                  some ((c0 :: ds), '>' :: rest) :=
                parseName_append ⟨c0, ds, rfl, hc0, hds⟩ (by
                  intro c hc
                  simp only [List.head?_cons] at hc
                  rw [← Option.some.inj hc]
                  exact isNameChar_false_of not_nameChar_gt)
              simp [parseElement, printNode, printElem, hc, hpn2, hat, hnodes,
                hend2, skipWs_cons (by decide : isWs '>' = false),
                List.append_assoc, List.cons_append]
        · -- content lists
          intro f hf nodes rest hwf hlen
          cases f with
          | zero => simp at hf
          | succ f' =>
            cases nodes with
            | nil =>
              simp [parseNodes, printNodes]
            | cons n0 ns =>
              have hn0 : WFNode n0 := match hwf with
                | .cons a _ _ => a
              have hns : WFNodes ns := match hwf with
                | .cons _ a _ => a
              have hadj : (∃ cs, n0 = .text cs) →
                  ∀ cs, ns.head? ≠ some (.text cs) := match hwf with
                | .cons _ _ a => a
              have hlen2 : (printNode n0).length + (printNodes ns).length + 2 =
                  n := by
                have h1 := hlen
                simp only [printNodes, List.length_append] at h1
                omega
              have hm : (printNodes ns).length + 2 < n := by
                have hp : 1 ≤ (printNode n0).length := by
                  cases n0 with
                  | text cs =>
                    cases hn0 with
                    | text hne hlegal =>
                      have h1 := escapeText_length_ge cs
                      have h2 : 1 ≤ cs.length := by
                        cases cs with
                        | nil => exact absurd rfl hne
                        | cons c cs' => simp
                      simp only [printNode]
                      omega
                  | elem name attrs content => simp [printNode, printElem]
                  | comment cs => simp [printNode]
                  | pi t d => simp [printNode]
                omega
              have hIH : parseNodes f' (printNodes ns ++ '<' :: '/' :: rest) =
                  some (ns, '<' :: '/' :: rest) :=
                (ih ((printNodes ns).length + 2) hm).2 f' (by omega) ns rest
                  hns rfl
              cases n0 with
              | text t =>
                cases hn0 with
                | text hne hlegal =>
                  have hadj' : ∀ cs, ns.head? ≠ some (.text cs) :=
                    hadj ⟨t, rfl⟩
                  cases t with
                  | nil => exact absurd rfl hne
                  | cons c t' =>
                    have hrest : (printNodes ns ++ '<' :: '/' :: rest) = [] ∨
                        (printNodes ns ++ '<' :: '/' :: rest).head? =
                          some '<' := by
                      cases ns with
                      | nil =>
                        right
                        simp [printNodes]
                      | cons n1 ns' =>
                        right
                        cases n1 with
                        | text cs =>
                          exfalso
                          exact hadj' cs rfl
                        | elem name attrs content =>
                          simp [printNodes, printNode, printElem, List.cons_append]
                        | comment cs =>
                          simp [printNodes, printNode, List.cons_append]
                        | pi t d =>
                          simp [printNodes, printNode, List.cons_append]
                    have hstop : ∀ f, 1 ≤ f →
                        parseCharData f (printNodes ns ++ '<' :: '/' :: rest) =
                          some ([], printNodes ns ++ '<' :: '/' :: rest) := by
                      cases ns with
                      | nil =>
                        intro f hf2
                        simpa [printNodes] using
                          parseCharData_stop_lt_cons (c := '/') (by decide) f hf2
                      | cons n1 ns' =>
                        cases n1 with
                        | text cs =>
                          intro f _
                          exfalso
                          exact hadj' cs rfl
                        | elem name attrs content =>
                          have hn1 : WFNode (.elem name attrs content) :=
                            match hns with
                            | .cons a _ _ => a
                          cases hn1 with
                          | elem hname1 hattrs1 hcontent1 =>
                            obtain ⟨c1, ds1, hq1, hc1, -⟩ := hname1
                            intro f hf2
                            cases f with
                            | zero => simp at hf2
                            | succ f'' =>
                              have hc1ne : c1 ≠ '!' :=
                                IsNameStart.ne_bang hc1
                              simp [parseCharData, printNodes, printNode,
                                printElem, hq1, hc1ne, List.append_assoc]
                        | comment cs =>
                          intro f hf2
                          simpa [printNodes, printNode] using
                            parseCharData_stop_comment
                              (r := (cs ++ '-' :: '-' :: '>' :: []) ++
                                (printNodes ns' ++ '<' :: '/' :: rest)) f hf2
                        | pi t d =>
                          intro f hf2
                          simpa [printNodes, printNode] using
                            parseCharData_stop_lt_cons (c := '?') (by decide) f hf2
                    have hcd : parseCharData f'
                        (escapeText (c :: t') ++
                          (printNodes ns ++ '<' :: '/' :: rest)) =
                        some (c :: t', printNodes ns ++ '<' :: '/' :: rest) :=
                      parseCharData_escapeText (c :: t') _ (by simp) hlegal
                        hrest hstop f' (by
                          have h1 := escapeText_length_ge (c :: t')
                          have hlink : (printNode (.text (c :: t'))).length =
                              (escapeText (c :: t')).length := by
                            simp [printNode]
                          omega)
                    rcases escapeTextChar_cases c with
                      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                      ⟨h1, h2, h3, h4, h5⟩
                    · subst h1
                      have hcdX : parseCharData f'
                          ('&' :: 'a' :: 'm' :: 'p' :: ';' :: (List.flatMap escapeTextChar t' ++
                            (printNodes ns ++ '<' :: '/' :: rest))) =
                          some ('&' :: t', printNodes ns ++ '<' :: '/' :: rest) :=
                        hcd
                      simp [parseNodes, printNodes, printNode, escapeText, h2,
                        List.append_assoc]
                      rw [hcdX]
                      simp [hIH]
                    · subst h1
                      have hcdX : parseCharData f'
                          ('&' :: 'l' :: 't' :: ';' :: (List.flatMap escapeTextChar t' ++
                            (printNodes ns ++ '<' :: '/' :: rest))) =
                          some ('<' :: t', printNodes ns ++ '<' :: '/' :: rest) :=
                        hcd
                      simp [parseNodes, printNodes, printNode, escapeText, h2,
                        List.append_assoc]
                      rw [hcdX]
                      simp [hIH]
                    · subst h1
                      have hcdX : parseCharData f'
                          ('&' :: 'g' :: 't' :: ';' :: (List.flatMap escapeTextChar t' ++
                            (printNodes ns ++ '<' :: '/' :: rest))) =
                          some ('>' :: t', printNodes ns ++ '<' :: '/' :: rest) :=
                        hcd
                      simp [parseNodes, printNodes, printNode, escapeText, h2,
                        List.append_assoc]
                      rw [hcdX]
                      simp [hIH]
                    · subst h1
                      have hcdX : parseCharData f'
                          ('&' :: '#' :: '1' :: '3' :: ';' :: (List.flatMap escapeTextChar t' ++
                            (printNodes ns ++ '<' :: '/' :: rest))) =
                          some ('\r' :: t', printNodes ns ++ '<' :: '/' :: rest) :=
                        hcd
                      simp [parseNodes, printNodes, printNode, escapeText, h2,
                        List.append_assoc]
                      rw [hcdX]
                      simp [hIH]
                    · have hcdX : parseCharData f'
                          (c :: (List.flatMap escapeTextChar t' ++
                            (printNodes ns ++ '<' :: '/' :: rest))) =
                          some (c :: t', printNodes ns ++ '<' :: '/' :: rest) := by
                        have h := hcd
                        rw [show escapeText (c :: t') = c :: escapeText t' by
                          simp [escapeText, h5]] at h
                        exact h
                      simp [parseNodes, printNodes, printNode, escapeText,
                        h5, h2, List.append_assoc]
                      rw [hcdX]
                      simp [hIH]
              | comment body =>
                cases hn0 with
                | comment hdd hde hlegal =>
                  have hcb : parseCommentBody
                      (body ++ '-' :: '-' :: '>' ::
                        (printNodes ns ++ '<' :: '/' :: rest)) =
                      some (body, printNodes ns ++ '<' :: '/' :: rest) :=
                    parseCommentBody_print body _ hdd hde hlegal
                  simp [parseNodes, printNodes, printNode, hcb, hIH]
              | pi t d =>
                cases hn0 with
                | pi hname hres hq hlegal hstart =>
                  have hpi : parsePI
                      (t ++ (if d = [] then ['?', '>']
                             else ' ' :: d ++ ['?', '>']) ++
                        (printNodes ns ++ '<' :: '/' :: rest)) =
                      some (.pi t d, printNodes ns ++ '<' :: '/' :: rest) :=
                    parsePI_print t d _ hname hres hq hlegal hstart
                  have hpi2 := hpi
                  rw [List.append_assoc] at hpi2
                  simp only [List.cons_append] at hpi2
                  simp [parseNodes, printNodes, printNode]
                  rw [hpi2]
                  simp [hIH]
              | elem name attrs content =>
                cases hn0 with
                | elem hname hattrs hcontent =>
                  obtain ⟨c0, ds, hq0, hc0, hds⟩ := hname
                  have hmE : (printNode (.elem name attrs content)).length <
                      n := by
                    omega
                  have hE : parseElement f'
                      (printNode (.elem name attrs content) ++
                        (printNodes ns ++ '<' :: '/' :: rest)) =
                      some (.elem name attrs content,
                        printNodes ns ++ '<' :: '/' :: rest) :=
                    (ih (printNode (.elem name attrs content)).length hmE).1
                      f' (by omega) name attrs content
                      (printNodes ns ++ '<' :: '/' :: rest)
                      (WFNode.elem ⟨c0, ds, hq0, hc0, hds⟩ hattrs hcontent) rfl
                  have hc0ne1 : c0 ≠ '/' := IsNameStart.ne_slash hc0
                  have hc0ne2 : c0 ≠ '!' := IsNameStart.ne_bang hc0
                  have hc0ne3 : c0 ≠ '?' := IsNameStart.ne_quest hc0
                  simp only [printNode, printElem, hq0, List.append_assoc,
                    List.cons_append] at hE
                  simp [parseNodes, printNodes, printNode, printElem, hq0,
                    hc0ne2, isNameStart_of hc0,
                    List.append_assoc]
                  rw [hE]
                  simp [hIH]

  intro n
  exact aux n n (Nat.le_refl n)

/-- The misc parser stops at a tag whose second character starts
    a name: that is an element start, not a comment or a
    processing instruction. -/
theorem parseMisc_stop {f : Nat} {c : Char} {cs : List Char}
    (hc : IsNameStart c) :
    parseMisc (f + 1) ('<' :: c :: cs) = some ([], '<' :: c :: cs) := by
  have h1 : c ≠ '!' := IsNameStart.ne_bang hc
  have h2 : c ≠ '?' := IsNameStart.ne_quest hc
  have h3 : skipWs ('<' :: c :: cs) = '<' :: c :: cs :=
    skipWs_cons (by decide)
  simp [parseMisc, h3, h1, h2]

/-- Prologs and epilogs round trip: printing a list of comments
    and processing instructions and parsing gives the list back,
    with the continuation reached after it. -/
theorem parseMisc_print :
    ∀ (ms : List Node) (rest : List Char),
      MiscOk ms →
      (∀ f, 1 ≤ f → parseMisc f rest = some ([], skipWs rest)) →
      ∀ f, (printNodes ms).length + 1 ≤ f →
        parseMisc f (printNodes ms ++ rest) = some (ms, skipWs rest) := by
  intro ms
  induction ms with
  | nil =>
    intro rest _ hstop f hf
    simp only [printNodes, List.nil_append]
    exact hstop f (by omega)
  | cons n ms ih =>
    intro rest hok hstop f hf
    have hokn : WFNode n ∧
        ((∃ cs, n = .comment cs) ∨ (∃ t d, n = .pi t d)) :=
      hok n (by simp)
    have hoktail : MiscOk ms :=
      fun m hm => hok m (by simp [hm])
    cases f with
    | zero => omega
    | succ f' =>
      rcases hokn with ⟨hwf, hkind⟩
      rcases hkind with ⟨cs, rfl⟩ | ⟨t, d, rfl⟩
      · cases hwf with
        | comment hdd hde hlegal =>
          have hcb : parseCommentBody
              (cs ++ '-' :: '-' :: '>' :: (printNodes ms ++ rest)) =
              some (cs, printNodes ms ++ rest) :=
            parseCommentBody_print cs _ hdd hde hlegal
          have hlen : (printNodes ms).length + 1 ≤ f' := by
            have h2 : (printNode (.comment cs)).length = cs.length + 7 := by
              simp [printNode, List.length_append]
            have h1 : (printNodes (.comment cs :: ms)).length =
                (printNode (.comment cs)).length +
                  (printNodes ms).length := by
              simp [printNodes, List.length_append]
            omega
          have hih := ih rest hoktail hstop f' hlen
          simp [parseMisc, printNodes, printNode, hcb, hih,
            skipWs_cons (show isWs '<' = false by decide),
            List.append_assoc]
      · cases hwf with
        | pi hname hres hq hlegal hstart =>
          have hpi : parsePI
              (t ++ (if d = [] then ['?', '>']
                    else ' ' :: d ++ ['?', '>']) ++
                (printNodes ms ++ rest)) =
              some (.pi t d, printNodes ms ++ rest) :=
            parsePI_print t d _ hname hres hq hlegal hstart
          have hlen : (printNodes ms).length + 1 ≤ f' := by
            have h2 : 2 ≤ (printNode (.pi t d)).length := by
              simp only [printNode, List.length_cons]
              omega
            have h1 : (printNodes (.pi t d :: ms)).length =
                (printNode (.pi t d)).length +
                  (printNodes ms).length := by
              simp [printNodes, List.length_append]
            omega
          have hpi2 := hpi
          rw [List.append_assoc] at hpi2
          simp only [List.cons_append] at hpi2
          have hih := ih rest hoktail hstop f' hlen
          simp [parseMisc, printNodes, printNode, hpi2, hih,
            skipWs_cons (show isWs '<' = false by decide),
            List.append_assoc]

/-! ## Line ends

The parser normalizes line ends before it reads. The print of a well
formed document holds no carriage return: text and attribute values
write one as a character reference, and comments and processing
instructions hold none. So normalization leaves the print as it is. -/

theorem normEol_cons_ne {c : Char} (h : c ≠ '\r') (rest : List Char) :
    normEol (c :: rest) = c :: normEol rest :=
  normEol.eq_4 c rest (fun _ e _ => h e) h

theorem normEol_of_noCR : ∀ (cs : List Char), '\r' ∉ cs → normEol cs = cs
  | [], _ => normEol.eq_1
  | c :: rest, h => by
    have hc : c ≠ '\r' := fun e => h (e ▸ List.mem_cons_self)
    have hr : '\r' ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    rw [normEol_cons_ne hc, normEol_of_noCR rest hr]

theorem noCR_escapeTextChar (c : Char) : '\r' ∉ escapeTextChar c := by
  rcases escapeTextChar_cases c with
    ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h4, h⟩
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]
    simp only [List.mem_singleton]
    exact fun e => h4 e.symm

theorem noCR_escapeAttrChar (c : Char) : '\r' ∉ escapeAttrChar c := by
  rcases escapeAttrChar_cases c with
    ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
    ⟨_, _, _, _, _, h6, h⟩
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]
    simp only [List.mem_singleton]
    exact fun e => h6 e.symm

theorem noCR_escapeText (cs : List Char) : '\r' ∉ escapeText cs := by
  simp only [escapeText, List.mem_flatMap, not_exists, not_and]
  intro c _
  exact noCR_escapeTextChar c

theorem noCR_escapeAttr (cs : List Char) : '\r' ∉ escapeAttr cs := by
  simp only [escapeAttr, List.mem_flatMap, not_exists, not_and]
  intro c _
  exact noCR_escapeAttrChar c

theorem not_nameChar_cr : ¬ IsNameChar '\r' :=
  not_nameChar_of_test (by decide)

theorem noCR_validName {cs : List Char} (h : ValidName cs) : '\r' ∉ cs := by
  obtain ⟨c, ds, rfl, hc, hds⟩ := h
  intro m
  rcases List.mem_cons.mp m with e | e
  · exact not_nameChar_cr (e ▸ IsNameStart.toNameChar hc)
  · exact not_nameChar_cr (hds _ e)

theorem noCR_printAttrs : ∀ (attrs : List (List Char × List Char)),
    AttrsOk attrs → '\r' ∉ printAttrs attrs
  | [], _ => by simp [printAttrs]
  | (k, v) :: rest, h => by
    have h1 := noCR_validName h.1
    have h2 := noCR_escapeAttr v
    have h3 := noCR_printAttrs rest h.2.2.2.2
    simp [printAttrs, h1, h2, h3]

mutual
theorem noCR_printNode : ∀ (n : Node), WFNode n → '\r' ∉ printNode n
  | .text cs, _ => by simpa [printNode] using noCR_escapeText cs
  | .elem name attrs content, h => by
    cases h with
    | elem hname hattrs hcontent =>
      have h1 := noCR_validName hname
      have h2 := noCR_printAttrs attrs hattrs
      have h3 := noCR_printNodes content hcontent
      simp only [printNode, printElem]
      split <;> simp [h1, h2, h3]
  | .comment cs, h => by
    cases h with
    | comment _ _ _ hcr => simp [printNode, hcr]
  | .pi t d, h => by
    cases h with
    | pi hname _ _ _ _ hcr =>
      have h1 := noCR_validName hname
      simp only [printNode]
      split <;> simp [h1, hcr]
theorem noCR_printNodes : ∀ (ns : List Node), WFNodes ns →
    '\r' ∉ printNodes ns
  | [], _ => by simp [printNodes]
  | n :: ns, h => by
    cases h with
    | cons hn hns _ =>
      have h1 := noCR_printNode n hn
      have h2 := noCR_printNodes ns hns
      simp [printNodes, h1, h2]
end

theorem noCR_printNodes_misc : ∀ (ns : List Node), MiscOk ns →
    '\r' ∉ printNodes ns
  | [], _ => by simp [printNodes]
  | n :: ns, h => by
    have h1 := noCR_printNode n (h n (by simp)).1
    have h2 := noCR_printNodes_misc ns (fun m hm => h m (by simp [hm]))
    simp [printNodes, h1, h2]

theorem noCR_print (d : Document) (hwf : WF d) : '\r' ∉ print d := by
  obtain ⟨hpro, hroot, _, hepi⟩ := hwf
  have h1 := noCR_printNodes_misc d.prolog hpro
  have h2 := noCR_printNode d.root hroot
  have h3 := noCR_printNodes_misc d.epilog hepi
  simp [print, h1, h2, h3]

/-- The plan's claim: printing a well formed document and parsing
    the print gives the same document back. -/
theorem parse_print (d : Document) (hwf : WF d) :
    parse (print d) = some d := by
  have hnorm : normEol (print d) = print d :=
    normEol_of_noCR _ (noCR_print d hwf)
  obtain ⟨hpro, hroot, ⟨name, attrs, content, hreq⟩, hepi⟩ := hwf
  rw [hreq] at hroot
  cases hroot with
  | elem hname hattrs hcontent =>
    obtain ⟨c0, ds, hq0, hc0, hds⟩ := hname
    have harg : printNode d.root ++ printNodes d.epilog =
        '<' :: c0 :: (ds ++ (printAttrs attrs ++
          (if content = [] then ['/', '>']
           else '>' :: (printNodes content ++ '<' :: '/' ::
             ((c0 :: ds) ++ ['>'])))) ++ printNodes d.epilog) := by
      rw [hreq, hq0]
      simp [printNode, printElem, List.append_assoc, List.cons_append]
    have hsw : skipWs (printNode d.root ++ printNodes d.epilog) =
        printNode d.root ++ printNodes d.epilog := by
      rw [harg]
      exact skipWs_cons (by decide)
    have hstoproot : ∀ f, 1 ≤ f →
        parseMisc f (printNode d.root ++ printNodes d.epilog) =
          some ([], skipWs (printNode d.root ++ printNodes d.epilog)) := by
      intro f hf
      cases f with
      | zero => omega
      | succ f' =>
        rw [harg, skipWs_cons (show isWs '<' = false by decide)]
        exact parseMisc_stop hc0
    have hstopnil : ∀ f, 1 ≤ f →
        parseMisc f [] = some ([], skipWs []) := by
      intro f hf
      cases f with
      | zero => omega
      | succ f' => simp [parseMisc, skipWs]
    have hpro' : parseMisc ((printNodes d.prolog ++
      (printNode d.root ++ printNodes d.epilog)).length + 1)
        (printNodes d.prolog ++
          (printNode d.root ++ printNodes d.epilog)) =
        some (d.prolog, skipWs (printNode d.root ++
          printNodes d.epilog)) :=
      parseMisc_print d.prolog _ hpro hstoproot _ (by
        simp only [List.length_append]; omega)
    have hroot' : parseElement ((printNodes d.prolog ++
      (printNode d.root ++ printNodes d.epilog)).length + 1)
        (printNode d.root ++ printNodes d.epilog) =
        some (d.root, printNodes d.epilog) := by
      rw [hreq]
      exact (elem_nodes (printNode (.elem name attrs content)).length).1
        _ (by
          have e : (printNode d.root).length =
              (printNode (.elem name attrs content)).length := by
            rw [hreq]
          simp only [List.length_append]; omega)
        name attrs content (printNodes d.epilog)
        (WFNode.elem ⟨c0, ds, hq0, hc0, hds⟩ hattrs hcontent) rfl
    have hepi' : parseMisc ((printNodes d.prolog ++
      (printNode d.root ++ printNodes d.epilog)).length + 1) (printNodes d.epilog) =
        some (d.epilog, skipWs []) := by
      have h := parseMisc_print d.epilog [] hepi hstopnil
        ((printNodes d.prolog ++
          (printNode d.root ++ printNodes d.epilog)).length + 1) (by
        simp only [List.length_append]; omega)
      simpa using h
    have hPd : print d = printNodes d.prolog ++
        (printNode d.root ++ printNodes d.epilog) := by
      simp [print, List.append_assoc]
    have hdoc : parseDocument ((printNodes d.prolog ++
      (printNode d.root ++ printNodes d.epilog)).length + 1)
        (printNodes d.prolog ++
          (printNode d.root ++ printNodes d.epilog)) = some d := by
      simp only [parseDocument, hpro', hsw, hroot', hepi', skipWs]
      rfl
    have hparse : parse (print d) = parseDocument ((printNodes d.prolog ++
      (printNode d.root ++ printNodes d.epilog)).length + 1) (print d) := by
      have e : (printNodes d.prolog ++
      (printNode d.root ++ printNodes d.epilog)).length + 1 = (print d).length + 1 := by
        simp only [print, List.length_append]; omega
      rw [e]
      show parseDocument ((normEol (print d)).length + 1) (normEol (print d)) = _
      rw [hnorm]
    rw [hparse, hPd]
    exact hdoc

end Xml.Proofs
