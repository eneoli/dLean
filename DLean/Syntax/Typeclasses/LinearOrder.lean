import DLean.Syntax.Definitions
import Mathlib.Order.Basic

instance : LinearOrder Variable where
  le v1 v2 :=
    match v1, v2 with
    | .variable n1, .variable n2 => n1 ≤ n2

  le_refl v :=
    match v with
    | .variable n => String.le_refl n

  le_trans v1 v2 v3 :=
    match v1, v2, v3 with
    | .variable n1, .variable n2, .variable n3 => fun a a_1 ↦ String.le_trans a a_1

  le_antisymm v1 v2 h1 h2 :=
    match v1, v2 with
    | .variable n1, .variable n2 =>
      by simp at *; have h := String.le_antisymm h1 h2; rw [h];

  le_total v1 v2 :=
    match v1, v2 with
    | .variable n1, .variable n2 => String.le_total n1 n2

  toDecidableEq := inferInstance
  toDecidableLE v1 v2 :=
    match v1, v2 with
    | .variable n1, .variable n2 => inferInstanceAs (Decidable (n1 ≤ n2))

theorem assignable_eq {a : Assignable}
                      {b: Assignable}
                      (h1 : a.baseVariable.name = b.baseVariable.name)
                      (h2 : a.orderOfDerivate = b.orderOfDerivate) : a = b := by
  sorry

instance lexLE_inst : LE (Nat × String) :=
  ⟨fun p q =>
    p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)
  ⟩

theorem lexLE_total (p q : Nat × String) :  p ≤ q ∨ q ≤ p := by
  cases p with
  | mk n1 s1 =>
    cases q with
    | mk n2 s2 =>
      by_cases h : n1 = n2
      ·
        subst h
        cases String.le_total s1 s2 with
        | inl hle => left; right; exact ⟨rfl, hle⟩
        | inr hle => right; right; exact ⟨rfl, hle⟩
      ·
        cases Nat.lt_or_gt_of_ne h with
        | inl hlt => left; left; exact hlt
        | inr hgt => right; left; exact hgt

instance : LinearOrder Assignable where
  le a b := a.orderOfDerivate < b.orderOfDerivate ∨
            (a.orderOfDerivate = b.orderOfDerivate) ∧ a.baseVariable.name ≤ b.baseVariable.name
  le_refl := by
    intro a
    have h1 : a.orderOfDerivate = a.orderOfDerivate := by rfl
    have h2 : a.baseVariable.name = a.baseVariable.name := by rfl
    right
    simp

  le_trans := by
    intros a b c h1 h2
    by_cases h  : a.orderOfDerivate < b.orderOfDerivate
    by_cases h' : b.orderOfDerivate < c.orderOfDerivate
    .
      apply Or.inl
      exact Nat.lt_trans h h'

    .
      apply Or.elim h2
      intro _
      contradiction
      intro h''
      cases' h'' with h''1 h''2
      rw[←h''1]
      exact Or.inl h
    .
      apply Or.elim h1
      intro _
      contradiction
      intro h'
      cases' h' with h'1 h'2
      apply Or.elim h2
      intro h'
      rw[h'1]
      exact Or.inl h'
      intro h''
      cases' h'' with h''1 h''2
      rw[h'1]
      rw[←h''1]
      exact Or.inr ⟨rfl, by exact String.le_trans h'2 h''2⟩

  le_antisymm := by
    intros a b h1 h2
    cases h1
    cases h2
    .
      next h h' =>
      exfalso
      exact Nat.lt_asymm h h'
    .
      next h h' =>
      exfalso
      cases' h' with h' _
      rw[h'] at h
      exact Nat.lt_irrefl _ h
    .
      next h =>
      cases' h with h h'
      apply Or.elim h2
      intro h2
      rw[h] at h2
      exfalso
      exact Nat.lt_irrefl _ h2
      intro h1
      cases' h1 with h1' h1''
      have h3 : a.baseVariable.name = b.baseVariable.name := by
        exact String.le_antisymm h' h1''
      exact assignable_eq h3 h

  le_total := by
    intros a b
    exact lexLE_total (a.orderOfDerivate, a.baseVariable.name) (b.orderOfDerivate, b.baseVariable.name)

  toDecidableEq := inferInstance
  toDecidableLE a1 a2 := inferInstanceAs (Decidable (a1.orderOfDerivate < a2.orderOfDerivate ∨ a1.orderOfDerivate = a2.orderOfDerivate ∧ a1.baseVariable.name ≤ a2.baseVariable.name))
