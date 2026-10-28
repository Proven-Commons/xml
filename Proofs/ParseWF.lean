/-
  Every document the parser accepts is well formed: `parse cs = some d`
  gives `WF d`, for every text `cs`. Together with the round trip,
  printing an accepted document gives a text that parses back to the
  same document, which is the plan's main claim as written.

  The proof goes layer by layer, as the parser does. For each reader
  it shows what the reader gives back (legal characters, a valid
  name, a comment body with no `--`, and so on), and that the text
  left over is made of characters of the text it was given. That
  second fact carries one more property through: the parser reads a
  text whose line ends were normalized, so it holds no carriage
  return, and neither does any part of it, so no comment body and no
  processing instruction data can hold one.

  The one property that is not local is that no two text runs stand
  next to each other in element content. The content reader takes
  all character data up to the next markup in one step, so the text
  after a text run is empty or starts with a less sign that does not
  open a CDATA section, and the content reader never starts its
  answer with a text run at such a text.
-/

import Xml
import Proofs.RoundTrip

namespace Xml.Proofs

open Xml

/-! ## Small facts -/

theorem sub_refl (cs : List Char) : cs ⊆ cs := fun _ h => h

theorem sub_cons {r cs : List Char} (c : Char) (h : r ⊆ cs) : r ⊆ c :: cs :=
  fun _ hx => List.mem_cons_of_mem _ (h hx)

theorem sub_trans {a b c : List Char} (h1 : a ⊆ b) (h2 : b ⊆ c) : a ⊆ c :=
  fun _ hx => h2 (h1 hx)

theorem sub_append_right (a b : List Char) : b ⊆ a ++ b :=
  fun _ hx => List.mem_append_right _ hx

theorem sub_append_left (a b : List Char) : a ⊆ a ++ b :=
  fun _ hx => List.mem_append_left _ hx

theorem toNat_ofNat_valid (n : Nat) (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  simp only [Char.ofNat, h, dite_true]
  rfl

/-- A character reference that the reader accepts names a legal
    character. -/
theorem charRefChar_legal {n : Nat} {c : Char} (h : charRefChar n = some c) :
    LegalChar c := by
  unfold charRefChar at h
  split at h
  · rename_i hn
    cases h
    have hv : n.isValidChar := by
      unfold Nat.isValidChar
      omega
    unfold LegalChar
    rw [toNat_ofNat_valid n hv]
    exact hn
  · cases h

theorem legal_of_test {c : Char} (h : isLegalChar c = true) : LegalChar c :=
  isLegalChar_iff.mp h

theorem legal_space : LegalChar ' ' := legal_of_test (by decide)

/-! ## Whitespace and names -/

theorem skipWs_sub : ∀ cs, skipWs cs ⊆ cs
  | [] => sub_refl _
  | c :: cs => by
    simp only [skipWs]
    split
    · exact sub_cons c (skipWs_sub cs)
    · exact sub_refl _

theorem skipWs_head : ∀ (cs : List Char) (c : Char),
    (skipWs cs).head? = some c → isWs c = false
  | [], c, h => by simp [skipWs] at h
  | d :: cs, c, h => by
    simp only [skipWs] at h
    split at h
    · exact skipWs_head cs c h
    · rename_i hd
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simpa using hd

theorem takeNameChars_spec : ∀ (cs ds r : List Char),
    takeNameChars cs = (ds, r) → cs = ds ++ r ∧ ∀ d ∈ ds, isNameChar d = true
  | [], ds, r, h => by
    simp only [takeNameChars, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | c :: cs, ds, r, h => by
    simp only [takeNameChars] at h
    split at h
    · rename_i hc
      rcases hp : takeNameChars cs with ⟨ds', r'⟩
      rw [hp] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := takeNameChars_spec cs ds' r' hp
      refine ⟨by simp [h1], ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with e | hd
      · rw [e]; exact hc
      · exact h2 d hd
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp

theorem parseName_spec {cs n r : List Char} (h : parseName cs = some (n, r)) :
    ValidName n ∧ cs = n ++ r := by
  match cs, h with
  | c :: rest, h =>
    simp only [parseName] at h
    split at h
    · rename_i hc
      rcases hp : takeNameChars rest with ⟨ds, r'⟩
      rw [hp] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := takeNameChars_spec rest ds r' hp
      exact ⟨⟨c, ds, rfl, isNameStart_iff.mp hc,
        fun x hx => isNameChar_iff.mp (h2 x hx)⟩, by simp [h1]⟩
    · cases h

theorem parseName_sub {cs n r : List Char} (h : parseName cs = some (n, r)) :
    r ⊆ cs := by
  obtain ⟨_, e⟩ := parseName_spec h
  rw [e]
  exact sub_append_right _ _

/-! ## References -/

theorem takeDigits_spec : ∀ (cs ds r : List Char),
    takeDigits cs = (ds, r) → cs = ds ++ r
  | [], ds, r, h => by
    simp only [takeDigits, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | c :: cs, ds, r, h => by
    simp only [takeDigits] at h
    split at h
    · rcases hp : takeDigits cs with ⟨ds', r'⟩
      rw [hp] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [takeDigits_spec cs ds' r' hp]
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

theorem takeHexDigits_spec : ∀ (cs ds r : List Char),
    takeHexDigits cs = (ds, r) → cs = ds ++ r
  | [], ds, r, h => by
    simp only [takeHexDigits, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | c :: cs, ds, r, h => by
    simp only [takeHexDigits] at h
    split at h
    · rcases hp : takeHexDigits cs with ⟨ds', r'⟩
      rw [hp] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [takeHexDigits_spec cs ds' r' hp]
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- A reference the reader accepts stands for a legal character, and
    the text after it is part of the text it was read from. -/
theorem parseRef_spec {cs : List Char} {ch : Char} {r : List Char}
    (h : parseRef cs = some (ch, r)) : LegalChar ch ∧ r ⊆ cs := by
  unfold parseRef at h
  split at h
  · cases h
    exact ⟨legal_of_test (by decide),
      sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _)))⟩
  · cases h
    exact ⟨legal_of_test (by decide),
      sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _)))⟩
  · cases h
    exact ⟨legal_of_test (by decide),
      sub_cons _ (sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _))))⟩
  · cases h
    exact ⟨legal_of_test (by decide), sub_cons _ (sub_cons _
      (sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _)))))⟩
  · cases h
    exact ⟨legal_of_test (by decide), sub_cons _ (sub_cons _
      (sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _)))))⟩
  · rename_i rest
    split at h
    · rcases hp : takeHexDigits rest.tail with ⟨ds, r1⟩
      rw [hp] at h
      have hsub : r1 ⊆ '#' :: rest := by
        have e := takeHexDigits_spec _ ds r1 hp
        intro x hx
        apply List.mem_cons_of_mem
        cases rest with
        | nil => simp at e; rw [e.2] at hx; exact absurd hx (by simp)
        | cons y ys =>
          simp only [List.tail_cons] at e
          rw [e]
          exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)
      split at h
      rename_i ds' r' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      split at h
      · rename_i r2
        rw [Option.map_eq_some_iff] at h
        obtain ⟨c, hc, e⟩ := h
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨charRefChar_legal hc,
          sub_trans (sub_cons ';' (sub_refl r2)) hsub⟩
      · cases h
    · rcases hp : takeDigits rest with ⟨ds, r1⟩
      rw [hp] at h
      have hsub : r1 ⊆ '#' :: rest := by
        rw [takeDigits_spec _ ds r1 hp]
        exact sub_cons _ (sub_append_right _ _)
      split at h
      rename_i ds' r' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      split at h
      · rename_i r2
        rw [Option.map_eq_some_iff] at h
        obtain ⟨c, hc, e⟩ := h
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨charRefChar_legal hc,
          sub_trans (sub_cons ';' (sub_refl r2)) hsub⟩
      · cases h
  · cases h

/-! ## Text, CDATA, comments, processing instruction data, values -/

/-- A pattern-matching map that puts a character in front of the
    first part of the result, undone. -/
theorem map_cons_some {o : Option (List Char × List Char)} {c : Char}
    {t r : List Char}
    (h : (o.map fun (x : List Char × List Char) => (c :: x.1, x.2)) = some (t, r)) :
    ∃ t', o = some (t', r) ∧ t = c :: t' := by
  cases o with
  | none => cases h
  | some p =>
    obtain ⟨t', r'⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨t', rfl, rfl⟩

theorem legal_cons {c : Char} {t : List Char} (hc : LegalChar c)
    (ht : ∀ x ∈ t, LegalChar x) : ∀ x ∈ c :: t, LegalChar x := by
  intro x hx
  rcases List.mem_cons.mp hx with e | hx
  · rw [e]; exact hc
  · exact ht x hx

theorem parseTextRun_spec : ∀ (f : Nat) (cs t r : List Char),
    parseTextRun f cs = some (t, r) → (∀ c ∈ t, LegalChar c) ∧ r ⊆ cs
  | 0, cs, t, r, h => by
    rw [parseTextRun] at h
    cases h
  | f + 1, [], t, r, h => by
    rw [parseTextRun] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, sub_refl _⟩
  | f + 1, c :: rest, t, r, h => by
    rw [parseTextRun] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, sub_refl _⟩
    · split at h
      · split at h
        · rename_i ch r1 hr
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨t', r2⟩, h1, e⟩ := h
          simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          obtain ⟨hl, hs⟩ := parseTextRun_spec f r1 t' r2 h1
          obtain ⟨hcl, hrs⟩ := parseRef_spec hr
          exact ⟨legal_cons hcl hl, sub_trans hs (sub_trans hrs (sub_cons _ (sub_refl _)))⟩
        · cases h
      · split at h
        · rename_i hb
          split at h
          · cases h
          · obtain ⟨t', h1, rfl⟩ := map_cons_some h
            obtain ⟨hl, hs⟩ := parseTextRun_spec f rest t' r h1
            rw [hb]
            exact ⟨legal_cons (legal_of_test (by decide)) hl, sub_cons _ hs⟩
        · split at h
          · rename_i hlc
            obtain ⟨t', h1, rfl⟩ := map_cons_some h
            obtain ⟨hl, hs⟩ := parseTextRun_spec f rest t' r h1
            exact ⟨legal_cons (legal_of_test hlc) hl, sub_cons _ hs⟩
          · cases h

theorem parseCDATABody_spec : ∀ (cs t r : List Char),
    parseCDATABody cs = some (t, r) → (∀ c ∈ t, LegalChar c) ∧ r ⊆ cs
  | [], t, r, h => by
    unfold parseCDATABody at h
    cases h
  | c :: rest, t, r, h => by
    unfold parseCDATABody at h
    split at h
    · rename_i heq
      cases heq
    · rename_i rest' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [heq]
      exact ⟨by simp, sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _)))⟩
    · rename_i c' rest' _ heq
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      split at h
      · rename_i hlc
        obtain ⟨t', h1, rfl⟩ := map_cons_some h
        obtain ⟨hl, hs⟩ := parseCDATABody_spec rest t' r h1
        exact ⟨legal_cons (legal_of_test hlc) hl, sub_cons _ hs⟩
      · cases h

/-- The text where character data stops: the end, or a less sign
    that does not open a CDATA section. -/
def StopCD (r : List Char) : Prop :=
  r = [] ∨ ∃ r', r = '<' :: r' ∧
    ∀ x, r' ≠ '!' :: '[' :: 'C' :: 'D' :: 'A' :: 'T' :: 'A' :: '[' :: x

theorem parseCharData_spec : ∀ (f : Nat) (cs t r : List Char),
    parseCharData f cs = some (t, r) →
      (∀ c ∈ t, LegalChar c) ∧ r ⊆ cs ∧ StopCD r
  | 0, cs, t, r, h => by
    unfold parseCharData at h
    cases h
  | f + 1, cs, t, r, h => by
    unfold parseCharData at h
    split at h
    · rename_i heq
      exact absurd heq (by omega)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, sub_refl _, Or.inl rfl⟩
    · rename_i fuel rest heq
      have hf : f = fuel := Nat.succ.inj heq
      subst hf
      split at h
      · rename_i t1 r1 h1
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨t2, r2⟩, h2, e⟩ := h
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        obtain ⟨hl1, hs1⟩ := parseCDATABody_spec rest t1 r1 h1
        obtain ⟨hl2, hs2, hst⟩ := parseCharData_spec f r1 t2 r2 h2
        refine ⟨?_, ?_, hst⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hl1 x hx
          · exact hl2 x hx
        · exact sub_trans hs2 (sub_trans hs1 (fun _ hx => by simp [hx]))
      · cases h
    · rename_i fuel rest hne heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp, sub_refl _, Or.inr ⟨rest, rfl, ?_⟩⟩
      intro x e
      exact hne x e
    · rename_i cs' _ _ fuel heq _ _ _
      have hf : f = fuel := Nat.succ.inj heq
      subst hf
      split at h
      · rename_i t1 r1 h1
        rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨t2, r2⟩, h2, e⟩ := h
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        obtain ⟨hl1, hs1⟩ := parseTextRun_spec f cs' t1 r1 h1
        obtain ⟨hl2, hs2, hst⟩ := parseCharData_spec f r1 t2 r2 h2
        refine ⟨?_, sub_trans hs2 hs1, hst⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hl1 x hx
        · exact hl2 x hx
      · cases h

theorem sub_cons_cons {a b : List Char} (c : Char) (h : a ⊆ b) :
    c :: a ⊆ c :: b := by
  intro x hx
  rcases List.mem_cons.mp hx with e | hx
  · rw [e]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (h hx)

theorem noDashDash_nil : NoDashDash [] := by
  intro pre suf e
  have := congrArg List.length e
  simp at this

theorem notDashEnd_nil : NotDashEnd [] := by
  intro pre e
  have := congrArg List.length e
  simp at this

/-- What the comment body reader gives back: a body with no `--`,
    not ending with `-`, of legal characters, made of characters of
    the text, and the text after the closing marks. The last part
    says how the body starts, which the induction needs: an empty
    body means the text started with the closing marks. -/
theorem parseCommentBody_spec : ∀ (cs b r : List Char),
    parseCommentBody cs = some (b, r) →
      NoDashDash b ∧ NotDashEnd b ∧ (∀ c ∈ b, LegalChar c) ∧ b ⊆ cs ∧
      r ⊆ cs ∧ ((b = [] ∧ cs.head? = some '-') ∨ (b ≠ [] ∧ b.head? = cs.head?))
  | [], b, r, h => by
    unfold parseCommentBody at h
    cases h
  | c :: rest, b, r, h => by
    unfold parseCommentBody at h
    split at h
    · rename_i hc
      split at h
      · rename_i r'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨noDashDash_nil, notDashEnd_nil, by simp, by simp, ?_,
          Or.inl ⟨rfl, by simp [hc]⟩⟩
        exact sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _)))
      · cases h
      · rename_i hn1 hn2
        obtain ⟨b', h1, rfl⟩ := map_cons_some h
        obtain ⟨hdd, hde, hl, hbs, hrs, hhead⟩ := parseCommentBody_spec rest b' r h1
        have hb' : b' ≠ [] ∧ b'.head? ≠ some '-' := by
          rcases hhead with ⟨_, hh⟩ | ⟨hne, hh⟩
          · exfalso
            cases rest with
            | nil => simp at hh
            | cons x xs =>
              simp only [List.head?_cons, Option.some.injEq] at hh
              subst hh
              exact hn2 xs rfl
          · refine ⟨hne, ?_⟩
            rw [hh]
            intro e
            cases rest with
            | nil => simp at e
            | cons x xs =>
              simp only [List.head?_cons, Option.some.injEq] at e
              subst e
              exact hn2 xs rfl
        subst hc
        refine ⟨?_, ?_, legal_cons (legal_of_test (by decide)) hl,
          sub_cons_cons _ hbs, sub_cons _ hrs, Or.inr ⟨by simp, rfl⟩⟩
        · intro pre suf e
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, true_and] at e
            exact hb'.2 (by rw [e]; rfl)
          | cons y pre' =>
            simp only [List.cons_append, List.cons.injEq] at e
            exact hdd pre' suf e.2
        · intro pre e
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq, true_and] at e
            exact hb'.1 e
          | cons y pre' =>
            simp only [List.cons_append, List.cons.injEq] at e
            exact hde pre' e.2
    · split at h
      · rename_i hc hlc
        obtain ⟨b', h1, rfl⟩ := map_cons_some h
        obtain ⟨hdd, hde, hl, hbs, hrs, _⟩ := parseCommentBody_spec rest b' r h1
        refine ⟨?_, ?_, legal_cons (legal_of_test hlc) hl,
          sub_cons_cons _ hbs, sub_cons _ hrs, Or.inr ⟨by simp, rfl⟩⟩
        · intro pre suf e
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at e
            exact hc e.1
          | cons y pre' =>
            simp only [List.cons_append, List.cons.injEq] at e
            exact hdd pre' suf e.2
        · intro pre e
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at e
            exact hc e.1
          | cons y pre' =>
            simp only [List.cons_append, List.cons.injEq] at e
            exact hde pre' e.2
      · cases h

theorem noQClose_nil : NoQClose [] := by
  intro pre suf e
  have := congrArg List.length e
  simp at this

/-- What the processing instruction data reader gives back: data
    with no `?>`, of legal characters, made of characters of the
    text, and the text after the closing marks; and how the data
    starts. -/
theorem parsePIData_spec : ∀ (cs d r : List Char),
    parsePIData cs = some (d, r) →
      NoQClose d ∧ (∀ c ∈ d, LegalChar c) ∧ d ⊆ cs ∧ r ⊆ cs ∧
      ((d = [] ∧ cs.head? = some '?') ∨ (d ≠ [] ∧ d.head? = cs.head?))
  | [], d, r, h => by
    unfold parsePIData at h
    cases h
  | c :: rest, d, r, h => by
    unfold parsePIData at h
    split at h
    · rename_i hc
      split at h
      · rename_i r'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨noQClose_nil, by simp, by simp,
          sub_cons _ (sub_cons _ (sub_refl _)), Or.inl ⟨rfl, by simp [hc]⟩⟩
      · rename_i hn
        obtain ⟨d', h1, rfl⟩ := map_cons_some h
        obtain ⟨hq, hl, hds, hrs, hhead⟩ := parsePIData_spec rest d' r h1
        subst hc
        refine ⟨?_, legal_cons (legal_of_test (by decide)) hl,
          sub_cons_cons _ hds, sub_cons _ hrs, Or.inr ⟨by simp, rfl⟩⟩
        intro pre suf e
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq, true_and] at e
          subst e
          rcases hhead with ⟨hne, _⟩ | ⟨_, hh⟩
          · exact List.cons_ne_nil _ _ hne
          · cases rest with
            | nil => simp at hh
            | cons x xs =>
              simp only [List.head?_cons, Option.some.injEq] at hh
              subst hh
              exact hn xs rfl
        | cons y pre' =>
          simp only [List.cons_append, List.cons.injEq] at e
          exact hq pre' suf e.2
    · split at h
      · rename_i hc hlc
        obtain ⟨d', h1, rfl⟩ := map_cons_some h
        obtain ⟨hq, hl, hds, hrs, _⟩ := parsePIData_spec rest d' r h1
        refine ⟨?_, legal_cons (legal_of_test hlc) hl,
          sub_cons_cons _ hds, sub_cons _ hrs, Or.inr ⟨by simp, rfl⟩⟩
        intro pre suf e
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at e
          exact hc e.1
        | cons y pre' =>
          simp only [List.cons_append, List.cons.injEq] at e
          exact hq pre' suf e.2
      · cases h

/-- What the attribute value reader gives back: legal characters,
    and the text after the closing quote. -/
theorem parseAttrValue_spec (q : Char) : ∀ (f : Nat) (cs v r : List Char),
    parseAttrValue q f cs = some (v, r) → (∀ c ∈ v, LegalChar c) ∧ r ⊆ cs
  | 0, cs, v, r, h => by
    rw [parseAttrValue] at h
    cases h
  | f + 1, [], v, r, h => by
    rw [parseAttrValue] at h
    cases h
  | f + 1, c :: rest, v, r, h => by
    rw [parseAttrValue] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, sub_cons _ (sub_refl _)⟩
    · split at h
      · cases h
      · split at h
        · split at h
          · rename_i ch r1 hr
            rw [Option.map_eq_some_iff] at h
            obtain ⟨⟨v', r2⟩, h1, e⟩ := h
            simp only [Prod.mk.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨hl, hs⟩ := parseAttrValue_spec q f r1 v' r2 h1
            obtain ⟨hcl, hrs⟩ := parseRef_spec hr
            exact ⟨legal_cons hcl hl,
              sub_trans hs (sub_trans hrs (sub_cons _ (sub_refl _)))⟩
          · cases h
        · split at h
          · obtain ⟨v', h1, rfl⟩ := map_cons_some h
            obtain ⟨hl, hs⟩ := parseAttrValue_spec q f rest v' r h1
            exact ⟨legal_cons legal_space hl, sub_cons _ hs⟩
          · split at h
            · rename_i hlc
              obtain ⟨v', h1, rfl⟩ := map_cons_some h
              obtain ⟨hl, hs⟩ := parseAttrValue_spec q f rest v' r h1
              exact ⟨legal_cons (legal_of_test hlc) hl, sub_cons _ hs⟩
            · cases h

/-! ## Processing instructions and attribute lists -/

theorem not_IsWs_of_false {c : Char} (h : isWs c = false) : ¬ IsWs c := by
  intro hw
  have : isWs c = true := by
    rcases hw with e | e | e | e <;> rw [e] <;> decide
  rw [this] at h
  cases h

/-- What the processing instruction reader gives back: an
    instruction, well formed when the text holds no carriage
    return, and the text after it. -/
theorem parsePI_spec {cs : List Char} {n : Node} {r : List Char}
    (h : parsePI cs = some (n, r)) :
    ('\r' ∉ cs → WFNode n) ∧ (∃ t d, n = .pi t d) ∧ r ⊆ cs := by
  unfold parsePI at h
  split at h
  · rename_i target r1 hpn
    obtain ⟨hvn, hcs⟩ := parseName_spec hpn
    split at h
    · cases h
    · rename_i hres
      split at h
      · rename_i r2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun _ => ?_, ⟨target, [], rfl⟩, ?_⟩
        · exact WFNode.pi hvn hres noQClose_nil (by simp) (Or.inl rfl) (by simp)
        · rw [hcs]
          exact sub_trans (sub_cons _ (sub_cons _ (sub_refl _))) (sub_append_right _ _)
      · rename_i c tl _
        split at h
        · split at h
          · rename_i d r2 hpd
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hq, hl, hds, hrs, hhead⟩ := parsePIData_spec _ d r2 hpd
            have hsk : skipWs (c :: tl) ⊆ cs := by
              rw [hcs]
              exact sub_trans (skipWs_sub _) (sub_append_right _ _)
            refine ⟨fun hcr => ?_, ⟨target, d, rfl⟩, sub_trans hrs hsk⟩
            refine WFNode.pi hvn hres hq hl ?_ (fun m => hcr (hsk (hds m)))
            rcases hhead with ⟨hd, _⟩ | ⟨_, hh⟩
            · exact Or.inl hd
            · right
              intro x xs e
              subst e
              exact not_IsWs_of_false (skipWs_head _ x (by rw [← hh]; rfl))
          · cases h
        · cases h
      · cases h
  · cases h

theorem AttrsOk_append : ∀ (acc : List (List Char × List Char)) (a v : List Char),
    AttrsOk acc → ValidName a → a ≠ xmlnsName → (∀ c ∈ v, LegalChar c) →
    (∀ kv ∈ acc, kv.1 ≠ a) → AttrsOk (acc ++ [(a, v)])
  | [], a, v, _, h1, h2, h3, _ => by
    simp only [List.nil_append, AttrsOk]
    exact ⟨h1, h2, h3, by simp, trivial⟩
  | kv :: rest, a, v, hok, h1, h2, h3, h4 => by
    simp only [List.cons_append, AttrsOk] at hok ⊢
    obtain ⟨g1, g2, g3, g4, g5⟩ := hok
    refine ⟨g1, g2, g3, ?_, AttrsOk_append rest a v g5 h1 h2 h3
      (fun k hk => h4 k (List.mem_cons_of_mem _ hk))⟩
    intro kv2 hkv2
    rcases List.mem_append.mp hkv2 with hk | hk
    · exact g4 kv2 hk
    · simp only [List.mem_singleton] at hk
      subst hk
      exact fun e => h4 kv List.mem_cons_self e.symm

/-- What the attribute reader gives back: on top of a list of
    attributes that meets `AttrsOk`, a list that meets it too, and
    the text after the tag. -/
theorem parseAttrs_spec : ∀ (f : Nat) (acc : List (List Char × List Char))
    (cs : List Char) (attrs : List (List Char × List Char)) (r : List Char)
    (b : Bool), parseAttrs f acc cs = some (attrs, r, b) → AttrsOk acc →
    AttrsOk attrs ∧ r ⊆ cs
  | 0, acc, cs, attrs, r, b, h, _ => by
    rw [parseAttrs] at h
    cases h
  | f + 1, acc, cs, attrs, r, b, h, hok => by
    rw [parseAttrs] at h
    have hsk := skipWs_sub cs
    split at h
    · rename_i rest heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [heq] at hsk
      exact ⟨hok, sub_trans (sub_cons _ (sub_cons _ (sub_refl _))) hsk⟩
    · rename_i rest heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [heq] at hsk
      exact ⟨hok, sub_trans (sub_cons _ (sub_refl _)) hsk⟩
    · split at h
      · split at h
        · rename_i aname r1 hpn
          obtain ⟨hvn, hcs⟩ := parseName_spec hpn
          have hr1 : r1 ⊆ cs := by
            rw [hcs] at hsk
            exact sub_trans (sub_append_right _ _) hsk
          split at h
          · cases h
          · rename_i hnx
            split at h
            · rename_i r2 heq2
              have hr2 : r2 ⊆ cs := by
                have := skipWs_sub r1
                rw [heq2] at this
                exact sub_trans (sub_trans (sub_cons _ (sub_refl _)) this) hr1
              split at h
              · rename_i r3 heq3
                have hr3 : r3 ⊆ cs := by
                  have := skipWs_sub r2
                  rw [heq3] at this
                  exact sub_trans (sub_trans (sub_cons _ (sub_refl _)) this) hr2
                split at h
                · rename_i v r4 hv
                  obtain ⟨hlv, hr4⟩ := parseAttrValue_spec _ f r3 v r4 hv
                  split at h
                  · cases h
                  · rename_i hany
                    have hd : ∀ kv ∈ acc, kv.1 ≠ aname := by
                      intro kv hkv e
                      apply hany
                      exact List.any_eq_true.mpr ⟨kv, hkv, by simp [e]⟩
                    obtain ⟨hA, hR⟩ := parseAttrs_spec f _ r4 attrs r b h
                      (AttrsOk_append acc aname v hok hvn hnx hlv hd)
                    exact ⟨hA, sub_trans hR (sub_trans hr4 hr3)⟩
                · cases h
              · rename_i r3 heq3
                have hr3 : r3 ⊆ cs := by
                  have := skipWs_sub r2
                  rw [heq3] at this
                  exact sub_trans (sub_trans (sub_cons _ (sub_refl _)) this) hr2
                split at h
                · rename_i v r4 hv
                  obtain ⟨hlv, hr4⟩ := parseAttrValue_spec _ f r3 v r4 hv
                  split at h
                  · cases h
                  · rename_i hany
                    have hd : ∀ kv ∈ acc, kv.1 ≠ aname := by
                      intro kv hkv e
                      apply hany
                      exact List.any_eq_true.mpr ⟨kv, hkv, by simp [e]⟩
                    obtain ⟨hA, hR⟩ := parseAttrs_spec f _ r4 attrs r b h
                      (AttrsOk_append acc aname v hok hvn hnx hlv hd)
                    exact ⟨hA, sub_trans hR (sub_trans hr4 hr3)⟩
                · cases h
              · cases h
            · cases h
        · cases h
      · cases h
    · cases h

/-! ## Elements and content -/

theorem map_cons_some_node {o : Option (List Node × List Char)} {n : Node}
    {ns : List Node} {r : List Char}
    (h : (o.map fun (x : List Node × List Char) => (n :: x.1, x.2)) = some (ns, r)) :
    ∃ ns', o = some (ns', r) ∧ ns = n :: ns' := by
  cases o with
  | none => cases h
  | some p =>
    obtain ⟨ns', r'⟩ := p
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ns', rfl, rfl⟩

/-- The element reader only ever gives back an element. -/
theorem parseElement_is_elem {f : Nat} {cs : List Char} {n : Node}
    {r : List Char} (h : parseElement f cs = some (n, r)) :
    ∃ nm a c, n = .elem nm a c := by
  cases f with
  | zero =>
    unfold parseElement at h
    cases h
  | succ f =>
    unfold parseElement at h
    iterate 8 (all_goals (try (split at h)))
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ⟨_, _, _, rfl⟩)

/-- At a text where character data stops, the content reader never
    starts its answer with a text run. This is what keeps two text
    runs from standing next to each other in the tree. -/
theorem nodes_head_not_text (f : Nat) (r : List Char) (ns : List Node)
    (r2 : List Char) (hst : StopCD r) (h : parseNodes f r = some (ns, r2)) :
    ∀ x, ns.head? ≠ some (.text x) := by
  cases f with
  | zero =>
    unfold parseNodes at h
    cases h
  | succ f =>
    unfold parseNodes at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro x e
      cases e
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro x e
      cases e
    · split at h
      · obtain ⟨ns', _, rfl⟩ := map_cons_some_node h
        intro x e
        cases e
      · cases h
    · exfalso
      rcases hst with e | ⟨r', e, hn⟩
      · cases e
      · simp only [List.cons.injEq, true_and] at e
        rename_i tail
        exact hn tail e.symm
    · split at h
      · rename_i n r1 hpi
        obtain ⟨_, ⟨t, d, rfl⟩, _⟩ := parsePI_spec hpi
        obtain ⟨ns', _, rfl⟩ := map_cons_some_node h
        intro x e
        cases e
      · cases h
    · split at h
      · split at h
        · rename_i n r1 hel
          obtain ⟨nm, a, c, rfl⟩ := parseElement_is_elem hel
          obtain ⟨ns', _, rfl⟩ := map_cons_some_node h
          intro x e
          cases e
        · cases h
      · cases h
    · cases h
    · exfalso
      rename_i h1 _ _ _ _ h6 h7
      rcases hst with e | ⟨r', e, _⟩
      · exact h1 e
      · cases r' with
        | nil => exact h7 e
        | cons c tl => exact h6 c tl e

/-- The element and content readers, together, by induction on the
    fuel: on a text with no carriage return, the element reader gives
    a well formed element, the content reader a well formed content
    list, and each leaves a part of the text. -/
theorem elem_nodes_wf : ∀ f,
    (∀ cs n r, parseElement f cs = some (n, r) → '\r' ∉ cs →
      WFNode n ∧ r ⊆ cs) ∧
    (∀ cs ns r, parseNodes f cs = some (ns, r) → '\r' ∉ cs →
      WFNodes ns ∧ r ⊆ cs)
  | 0 => by
    refine ⟨fun cs n r h _ => ?_, fun cs ns r h _ => ?_⟩
    · unfold parseElement at h
      cases h
    · unfold parseNodes at h
      cases h
  | f + 1 => by
    obtain ⟨ihE, ihN⟩ := elem_nodes_wf f
    constructor
    · intro cs n r h hcr
      unfold parseElement at h
      split at h
      · rename_i rest
        split at h
        · rename_i name r1 hpn
          obtain ⟨hvn, hcs⟩ := parseName_spec hpn
          have hr1 : r1 ⊆ '<' :: rest := by
            rw [hcs]
            exact sub_cons _ (sub_append_right _ _)
          split at h
          · rename_i attrs r2 hat
            obtain ⟨hA, hr2⟩ := parseAttrs_spec f [] r1 attrs r2 true hat trivial
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨WFNode.elem hvn hA WFNodes.nil, sub_trans hr2 hr1⟩
          · rename_i attrs r2 hat
            obtain ⟨hA, hr2⟩ := parseAttrs_spec f [] r1 attrs r2 false hat trivial
            split at h
            · rename_i content r3 hn
              obtain ⟨hW, hr3⟩ := ihN r2 content r3 hn
                (fun m => hcr (hr1 (hr2 m)))
              split at h
              · rename_i r4
                split at h
                · rename_i ename r5 hpe
                  have hr5 : r5 ⊆ r4 := parseName_sub hpe
                  split at h
                  · rename_i r6 heq6
                    split at h
                    · simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      refine ⟨WFNode.elem hvn hA hW, ?_⟩
                      have h6 : r6 ⊆ skipWs r5 := by
                        rw [heq6]
                        exact sub_cons _ (sub_refl _)
                      exact sub_trans h6 (sub_trans (skipWs_sub r5)
                        (sub_trans hr5 (sub_trans
                          (sub_cons _ (sub_cons _ (sub_refl _)))
                          (sub_trans hr3 (sub_trans hr2 hr1)))))
                    · cases h
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · intro cs ns r h hcr
      unfold parseNodes at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨WFNodes.nil, sub_refl _⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨WFNodes.nil, sub_refl _⟩
      · rename_i rest
        split at h
        · rename_i body r1 hcb
          obtain ⟨hdd, hde, hl, hbs, hr1, _⟩ := parseCommentBody_spec rest body r1 hcb
          have hrest : rest ⊆ '<' :: '!' :: '-' :: '-' :: rest :=
            sub_cons _ (sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _))))
          obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
          obtain ⟨hW, hr⟩ := ihN r1 ns' r h1 (fun m => hcr (hrest (hr1 m)))
          refine ⟨WFNodes.cons
            (WFNode.comment hdd hde hl (fun m => hcr (hrest (hbs m)))) hW ?_,
            sub_trans hr (sub_trans hr1 hrest)⟩
          intro ⟨x, e⟩
          cases e
        · cases h
      · split at h
        · rename_i t r1 hcd
          obtain ⟨hl, hr1, hst⟩ := parseCharData_spec f _ t r1 hcd
          split at h
          · obtain ⟨hW, hr⟩ := ihN r1 ns r h (fun m => hcr (hr1 m))
            exact ⟨hW, sub_trans hr hr1⟩
          · rename_i hne
            obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
            obtain ⟨hW, hr⟩ := ihN r1 ns' r h1 (fun m => hcr (hr1 m))
            exact ⟨WFNodes.cons (WFNode.text hne hl) hW
              (fun _ => nodes_head_not_text f r1 ns' r hst h1),
              sub_trans hr hr1⟩
        · cases h
      · rename_i rest
        split at h
        · rename_i n r1 hpi
          obtain ⟨hwf, ⟨t, d, rfl⟩, hr1⟩ := parsePI_spec hpi
          have hrest : rest ⊆ '<' :: '?' :: rest :=
            sub_cons _ (sub_cons _ (sub_refl _))
          obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
          obtain ⟨hW, hr⟩ := ihN r1 ns' r h1 (fun m => hcr (hrest (hr1 m)))
          refine ⟨WFNodes.cons (hwf (fun m => hcr (hrest m))) hW ?_,
            sub_trans hr (sub_trans hr1 hrest)⟩
          intro ⟨x, e⟩
          cases e
        · cases h
      · split at h
        · split at h
          · rename_i n r1 hel
            obtain ⟨hwf, hr1⟩ := ihE _ n r1 hel hcr
            obtain ⟨nm, a, c, rfl⟩ := parseElement_is_elem hel
            obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
            obtain ⟨hW, hr⟩ := ihN r1 ns' r h1 (fun m => hcr (hr1 m))
            refine ⟨WFNodes.cons hwf hW ?_, sub_trans hr hr1⟩
            intro ⟨x, e⟩
            cases e
          · cases h
        · cases h
      · cases h
      · split at h
        · rename_i t r1 hcd
          obtain ⟨hl, hr1, hst⟩ := parseCharData_spec f _ t r1 hcd
          split at h
          · obtain ⟨hW, hr⟩ := ihN r1 ns r h (fun m => hcr (hr1 m))
            exact ⟨hW, sub_trans hr hr1⟩
          · rename_i hne
            obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
            obtain ⟨hW, hr⟩ := ihN r1 ns' r h1 (fun m => hcr (hr1 m))
            exact ⟨WFNodes.cons (WFNode.text hne hl) hW
              (fun _ => nodes_head_not_text f r1 ns' r hst h1),
              sub_trans hr hr1⟩
        · cases h

/-! ## Prolog, epilog, document -/

theorem parseMisc_spec : ∀ (f : Nat) (cs : List Char) (ns : List Node)
    (r : List Char), parseMisc f cs = some (ns, r) → '\r' ∉ cs →
    MiscOk ns ∧ r ⊆ cs
  | 0, cs, ns, r, h, _ => by
    unfold parseMisc at h
    cases h
  | f + 1, cs, ns, r, h, hcr => by
    unfold parseMisc at h
    dsimp only at h
    have hsk := skipWs_sub cs
    split at h
    · rename_i rest heq
      split at h
      · rename_i body r1 hcb
        obtain ⟨hdd, hde, hl, hbs, hr1, _⟩ := parseCommentBody_spec rest body r1 hcb
        have hrest : rest ⊆ cs := by
          rw [heq] at hsk
          exact sub_trans
            (sub_cons _ (sub_cons _ (sub_cons _ (sub_cons _ (sub_refl _))))) hsk
        obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
        obtain ⟨hM, hr⟩ := parseMisc_spec f r1 ns' r h1
          (fun m => hcr (hrest (hr1 m)))
        refine ⟨?_, sub_trans hr (sub_trans hr1 hrest)⟩
        intro n hn
        rcases List.mem_cons.mp hn with e | hn
        · subst e
          exact ⟨WFNode.comment hdd hde hl (fun m => hcr (hrest (hbs m))),
            Or.inl ⟨body, rfl⟩⟩
        · exact hM n hn
      · cases h
    · rename_i rest heq
      split at h
      · rename_i n r1 hpi
        obtain ⟨hwf, ⟨t, d, rfl⟩, hr1⟩ := parsePI_spec hpi
        have hrest : rest ⊆ cs := by
          rw [heq] at hsk
          exact sub_trans (sub_cons _ (sub_cons _ (sub_refl _))) hsk
        obtain ⟨ns', h1, rfl⟩ := map_cons_some_node h
        obtain ⟨hM, hr⟩ := parseMisc_spec f r1 ns' r h1
          (fun m => hcr (hrest (hr1 m)))
        refine ⟨?_, sub_trans hr (sub_trans hr1 hrest)⟩
        intro n hn
        rcases List.mem_cons.mp hn with e | hn
        · subst e
          exact ⟨hwf (fun m => hcr (hrest m)), Or.inr ⟨t, d, rfl⟩⟩
        · exact hM n hn
      · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun n hn => absurd hn List.not_mem_nil, hsk⟩

theorem parseDocument_wf {f : Nat} {cs : List Char} {d : Document}
    (h : parseDocument f cs = some d) (hcr : '\r' ∉ cs) : WF d := by
  unfold parseDocument at h
  split at h
  · rename_i prolog r1 hm
    obtain ⟨hP, hr1⟩ := parseMisc_spec f cs prolog r1 hm hcr
    split at h
    · rename_i root r2 he
      obtain ⟨hR, hr2⟩ := (elem_nodes_wf f).1 r1 root r2 he (fun m => hcr (hr1 m))
      obtain ⟨nm, a, c, hshape⟩ := parseElement_is_elem he
      split at h
      · rename_i epilog r3 hm2
        obtain ⟨hE, _⟩ := parseMisc_spec f r2 epilog r3 hm2
          (fun m => hcr (hr1 (hr2 m)))
        split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨hP, hR, ⟨nm, a, c, hshape⟩, hE⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- The normalized text holds no carriage return. -/
theorem normEol_noCR (cs : List Char) : '\r' ∉ normEol cs := by
  induction cs using normEol.induct with
  | case1 => simp [normEol.eq_1]
  | case2 rest ih =>
    rw [normEol.eq_2]
    intro m
    rcases List.mem_cons.mp m with e | m
    · cases e
    · exact ih m
  | case3 rest hrest ih =>
    rw [normEol.eq_3 _ hrest]
    intro m
    rcases List.mem_cons.mp m with e | m
    · cases e
    · exact ih m
  | case4 c rest _ hc ih =>
    rw [normEol_cons_ne hc]
    intro m
    rcases List.mem_cons.mp m with e | m
    · exact hc e.symm
    · exact ih m

/-- Every document the parser accepts is well formed. -/
theorem parse_wf (cs : List Char) (d : Document) (h : parse cs = some d) :
    WF d :=
  parseDocument_wf h (normEol_noCR cs)

/-- The plan's main claim: printing a parsed document gives a text
    that parses to the same document. -/
theorem print_parse (cs : List Char) (d : Document) (h : parse cs = some d) :
    parse (print d) = some d :=
  parse_print d (parse_wf cs d h)

end Xml.Proofs
