import DLean.Syntax.Syntax
import DLean.Axioms.Axioms
import DLean.USubst.Subst
import DLean.USubst.Semantics

import Mathlib.Data.Finset.Defs

open Semantics
open Embedding

#check [Formula| [x’ = f(x) & q(x)]q(x)]
theorem DW_example : sound [Formula| [x’ = 1 & x > 1] x > 1] := by
  let σ : Subst := ⟨[
      .unitFun  {name := "F", taboo := ∅} [Term| 1]        (by cbv),
      .unitPred {name := "Q", taboo := ∅} [Formula| x > 1] (by cbv),
    ], ?_⟩

  .
    apply US (σ := σ) ?_ DW
    cbv -- admissibility check, always computable
  .
    -- Subst is valid
    cbv
    grind

example : sound [Formula| ∀x, [x := f] p(x) ↔ p(f)] := by
  unfold sound

  let σ : Subst := ⟨[], by sorry⟩

  -- have assign := assign
  -- unfold sound at assign

  -- have := Forall assign
-- theorem US_rule {σ : Subst}
--                 (premises : List (Formula × Formula))
--                 (Ψ Ψ' : Formula)
--                 (hp : ∀ Φ ∈ premises, Formula.applySubst σ Φ.1 = Φ.2)
--                 (hΨ : Formula.applySubst σ Ψ = Ψ')
--                 (hσ : Subst.freeVars σ .none = ∅)
--   : (∀ (i : Interpretation), (∀ (v : State) (Φ : Formula × Formula), Φ ∈ premises → v ∈ Formula.denote i Φ.1) → (∀ (v : State), v ∈ Formula.denote i Ψ))
--   → (∀ (i : Interpretation), (∀ (v : State) (Φ : Formula × Formula), Φ ∈ premises → v ∈ Formula.denote i Φ.2) → (∀ (v : State), v ∈ Formula.denote i Ψ')) := by

-- theorem Forall : ∀ i,
--     (∀ s, s ∈ [Formula| p(x)].denote i)
--     ----------------------------------------
--   → (∀ s, s ∈ [Formula| ∀ x, p(x)].denote i) :=

  let σ : Subst := ⟨[
    .pred ⟨"p", 1⟩      [Formula| [x := f]p (x) ↔ p (f)],
  ], by cbv ; grind⟩

  -- have := US_rule
  --           (σ := σ)
  --           (premises := [⟨[Formula| p(x)], [Formula| [x := f]p(x) ↔ p(f)]⟩])
  --           (Ψ        := [Formula| ∀x, p(x)])
  --           (Ψ'       := [Formula| ∀x, [x := f]p(x) ↔ p(f)])
  --           (by simp_all[σ] ; cbv)
  --           (by simp_all[σ] ; cbv ; congr ; sorry)
  --           (by cbv ; congr )

  -- apply US (σ := σ) ?_ Forall
  sorry

example : sound [Formula| ([v := 2]⟨?v ≥ 1⟩true)] := by
  let σ : Subst := ⟨[
  ], by cbv ; grind⟩

  apply US (σ := σ) ?_ assign
  sorry

example : sound [Formula| [x := 1][x := 2] x ≥ 1] := by
  sorry

example : sound [Formula| [x := 1 ; x := 2] x ≥ 1] := by

  have : sound [Formula| ([x := 1 ; x := 2] x ≥ 1)
                       ↔ ([x := 1] [x := 2] x ≥ 1)] := by
    let σ : Subst := ⟨[
      .prog     ⟨"a"⟩                      [Program| x := 1],
      .prog     ⟨"b"⟩                      [Program| x := 2],
      .pred     ⟨"p", 1⟩                   [Formula| ·₀ ≥ 1],
      .unitPred {name := "P", taboo := ∅} [Formula| x ≥ 1] (by cbv),
    ], by cbv ; grind⟩

    apply US (σ := σ) ?_ boxSeq
    cbv



  intros i s
  unfold sound at this
  simp[Formula.denote_equiv] at this
  simp[this]

  clear this

  have : sound [Formula| ([x := 1][x := 2] x ≥ 1) ↔ ([x := 2] x ≥ 1)] := by
    let σ : Subst := ⟨[
      .fn   (.udef "f" 0) [Term| 1],
      .pred ⟨"p", 1⟩      [Formula| [x := 2] x ≥ 1],
    ], by cbv ; grind⟩

    apply US (σ := σ) ?_ assign
    cbv

  unfold sound at this
  simp[Formula.denote_equiv] at this
  simp[this]
  clear this


  -- [Formula| [x:=f()]p(x) ↔ p(f())]
  have : sound [Formula| ([x := 2] x ≥ 1) ↔ (2 ≥ 1)] := by
    let σ : Subst := ⟨[
      .fn   (.udef "f" 0) [Term| 2],
      .pred ⟨"p", 1⟩      [Formula| ·₀ ≥ 1],
    ], by cbv ; grind⟩

    apply US (σ := σ) ?_ assign
    cbv

  unfold sound at this
  simp[Formula.denote_equiv] at this
  simp[this]
  clear this

  simp_all[Formula.denote, Term.denote]

-- v≥0∧A≥0 → [x'=v,v'=A&true] v≥0

#check [Formula| [a;b]p(x) ↔ [a][b]p(x)]

example : sound [Formula| [x’ = v ; v’ = A & true] v ≥ 0] := by

  -- [Formula| [a;b]p(x) ↔ [a][b]p(x)]
  have : sound [Formula| ([x’ = v ; v’ = A]v ≥ 0)
                       ↔ ([x’ = v] [v’ = A]v ≥ 0)] := by
    let σ : Subst := ⟨[
      .prog ⟨"a"⟩                           [Program| x’ = v],
      .prog ⟨"b"⟩                           [Program| v’ = A & true],
      .unitPred {name := "P",  taboo := ∅} [Formula| v ≥ 0] (by cbv),
      -- .pred ⟨"p", 1⟩      [Formula| ·₀ ≥ 0],
      -- .fn   (.udef "x" 0) [Term| v],
    ], by cbv ; grind⟩

    apply US (σ := σ) ?_ boxSeq
    cbv

  have : sound [Formula| [x’ = v][v’ = A & true]⟨?v ≥ 0⟩true] := by
    sorry

  unfold sound at this
  simp[Formula.denote_equiv] at this

  have : sound [Formula| (([x’ = v ; v’ = A & true]⟨?v ≥ 0⟩ true) ↔ ([x’ = v][v’ = A & true]⟨?v ≥ 0⟩ true))
                       ↔ (([x’ = v ; v’ = A & true] v ≥ 0) ↔ ([x’ = v][v’ = A & true] v ≥ 0))] := by

    let σ : Subst := ⟨[
      .prog ⟨"a"⟩         [Program| x’ = v],
      .prog ⟨"b"⟩         [Program| v’ = A & true],
      .prog ⟨"k"⟩         [Program| ?v ≥ 0],
      -- .pred ⟨"p", 1⟩      [Formula| ·₀ ≥ 0],
      -- .fn   (.udef "x" 0) [Term| v],
    ], by cbv ; grind⟩

    apply US (σ := σ) ?_ boxSeq

    sorry
  sorry
