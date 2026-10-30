/-
  Line ends: the parser normalizes them before it reads, as XML 1.0
  section 2.11 requires. The lemmas here say how the normalization
  `normEol` acts on a text made of two parts, and the two theorems
  at the end say what that means for `parse`: a carriage return
  followed by a line feed reads as one line feed, and a carriage
  return followed by anything else reads as a line feed.
-/

import Xml
import Xml.Proofs.RoundTrip

namespace Xml.Proofs

open Xml

/-! ## Line ends in a text with a printed head -/

/-- Normalizing a text whose head holds no carriage return leaves
    the head as it is. -/
theorem normEol_append_noCR : ∀ (A B : List Char), '\r' ∉ A →
    normEol (A ++ B) = A ++ normEol B
  | [], _, _ => rfl
  | c :: A, B, h => by
    have hc : c ≠ '\r' := fun e => h (e ▸ List.mem_cons_self)
    have hA : '\r' ∉ A := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, normEol_cons_ne hc, normEol_append_noCR A B hA,
      List.cons_append]

/-- The head of a normalized text is the head of the text, or a
    line feed. -/
theorem normEol_head (cs : List Char) (c : Char)
    (h : (normEol cs).head? = some c) : cs.head? = some c ∨ c = '\n' := by
  match cs with
  | [] => simp [normEol] at h
  | '\r' :: '\n' :: rest =>
    rw [normEol.eq_2] at h
    exact Or.inr (Option.some.inj h).symm
  | '\r' :: [] =>
    rw [normEol.eq_3 _ (by intro r e; cases e)] at h
    exact Or.inr (Option.some.inj h).symm
  | '\r' :: d :: rest =>
    by_cases hd : d = '\n'
    · subst hd
      rw [normEol.eq_2] at h
      exact Or.inr (Option.some.inj h).symm
    · rw [normEol.eq_3 _ (by intro r e; exact hd (List.cons.inj e).1)] at h
      exact Or.inr (Option.some.inj h).symm
  | d :: rest =>
    by_cases hd : d = '\r'
    · subst hd
      cases rest with
      | nil =>
        rw [normEol.eq_3 _ (by intro r e; cases e)] at h
        exact Or.inr (Option.some.inj h).symm
      | cons e rest' =>
        by_cases he : e = '\n'
        · subst he
          rw [normEol.eq_2] at h
          exact Or.inr (Option.some.inj h).symm
        · rw [normEol.eq_3 _ (by intro r e2; exact he (List.cons.inj e2).1)] at h
          exact Or.inr (Option.some.inj h).symm
    · rw [normEol_cons_ne hd] at h
      exact Or.inl h

/-- A text whose head is not a name character keeps that property
    when its line ends are normalized. -/
theorem normEol_head_not_name (cs : List Char)
    (h : ∀ c, cs.head? = some c → ¬ IsNameChar c) :
    ∀ c, (normEol cs).head? = some c → isNameChar c = false := by
  intro c hc
  rcases normEol_head cs c hc with h1 | h1
  · exact isNameChar_false_of (h c h1)
  · subst h1
    decide

/-- Normalizing a text made of two parts is normalizing each part,
    when the first part does not end with a carriage return (which
    could pair with a line feed at the head of the second). -/
theorem normEol_append (A B : List Char) (h : ∀ x, A ≠ x ++ ['\r']) :
    normEol (A ++ B) = normEol A ++ normEol B := by
  induction A using normEol.induct with
  | case1 => simp [normEol.eq_1]
  | case2 rest ih =>
    have h' : ∀ x, rest ≠ x ++ ['\r'] := by
      intro x e
      exact h ('\r' :: '\n' :: x) (by rw [e]; rfl)
    rw [List.cons_append, List.cons_append, normEol.eq_2, normEol.eq_2,
      ih h', List.cons_append]
  | case3 rest hrest ih =>
    cases rest with
    | nil => exact absurd rfl (h [])
    | cons d ds =>
      have h' : ∀ x, d :: ds ≠ x ++ ['\r'] := by
        intro x e
        exact h ('\r' :: x) (by rw [e]; rfl)
      have hne : ∀ r, d :: ds ++ B ≠ '\n' :: r := by
        intro r e
        rw [List.cons_append] at e
        exact hrest ds (by rw [(List.cons.inj e).1])
      rw [List.cons_append, normEol.eq_3 _ hne, normEol.eq_3 _ hrest,
        ih h', List.cons_append]
  | case4 c rest _ hc ih =>
    have h' : ∀ x, rest ≠ x ++ ['\r'] := by
      intro x e
      exact h (c :: x) (by rw [e]; rfl)
    rw [List.cons_append, normEol_cons_ne hc, normEol_cons_ne hc,
      ih h', List.cons_append]

/-- A carriage return followed by a line feed reads as one line
    feed, wherever it stands, unless the text before it ends with
    a carriage return (which would pair with the line feed
    first). -/
theorem crlf_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') :
    parse (pre ++ '\r' :: '\n' :: post) = parse (pre ++ '\n' :: post) := by
  have h : ∀ x, pre ≠ x ++ ['\r'] := by
    intro x e
    exact hpre (List.getLast?_eq_some_iff.mpr ⟨x, e⟩)
  have e1 : normEol (pre ++ '\r' :: '\n' :: post) =
      normEol (pre ++ '\n' :: post) := by
    rw [normEol_append _ _ h, normEol_append _ _ h, normEol.eq_2,
      normEol_cons_ne (by decide)]
  show parseDocument ((normEol _).length + 1) (normEol _) =
    parseDocument ((normEol _).length + 1) (normEol _)
  rw [e1]

/-- A carriage return not followed by a line feed reads as a line
    feed, wherever it stands, unless the text before it ends with
    a carriage return. -/
theorem cr_reads_as_lf (pre post : List Char)
    (hpre : pre.getLast? ≠ some '\r') (hpost : post.head? ≠ some '\n') :
    parse (pre ++ '\r' :: post) = parse (pre ++ '\n' :: post) := by
  have h : ∀ x, pre ≠ x ++ ['\r'] := by
    intro x e
    exact hpre (List.getLast?_eq_some_iff.mpr ⟨x, e⟩)
  have hp : ∀ r, post ≠ '\n' :: r := by
    intro r e
    rw [e] at hpost
    exact hpost rfl
  have e1 : normEol (pre ++ '\r' :: post) = normEol (pre ++ '\n' :: post) := by
    rw [normEol_append _ _ h, normEol_append _ _ h,
      normEol.eq_3 _ (fun r e => hp r e), normEol_cons_ne (by decide)]
  show parseDocument ((normEol _).length + 1) (normEol _) =
    parseDocument ((normEol _).length + 1) (normEol _)
  rw [e1]

end Xml.Proofs
