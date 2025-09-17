import Mathlib.Data.Multiset.Basic

import DLean.Syntax.Syntax
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Embedding.Shallow

open Semantics
open Embedding

structure Sequent where
  left : Multiset Formula
  right : Multiset Formula

infixr:66 " ⊢ " => Sequent.mk

def semantics (Γ : Multiset Formula) (Δ : Multiset Formula) : Prop := match Γ.toList , Δ.toList with
  | [], [] => true → false
  | [], q::qs => ∀ (i : Interpretation) (s : State),
                   true → qs.foldr (fun p a => a ∨ Formula.eval i s p) (q.eval i s)
  | p::ps, [] => ∀ (i : Interpretation) (s : State),
                   ps.foldr (fun p a => a ∧ Formula.eval i s p) (p.eval i s) → false
  | p::ps, q::qs => ∀ (i : Interpretation) (s : State),
                   ps.foldr (fun p a => a ∧ Formula.eval i s p) (p.eval i s)
                   → qs.foldr (fun p a => a ∨ Formula.eval i s p) (q.eval i s)

-- TODO Joscha does not like the name
-- TODO: Eval + Theorems for axioms instead?
inductive Provable : Sequent → Prop where
  | semantical : {Γ Δ : Multiset Formula}
               → semantics Γ Δ
               → Provable (Γ ⊢ Δ)

  -- Base cases

  | id : {Γ Δ : Multiset Formula}
       → {Φ : Formula}
       → Φ ∈ Γ
       → Φ ∈ Δ
       → Provable (Γ ⊢ Δ)

  | trueR : {Γ Δ : Multiset Formula}
          → Formula.True ∈ Δ
          → Provable (Γ ⊢ Δ)

  | falseL : {Γ Δ : Multiset Formula}
           → Formula.False ∈ Γ
           → Provable (Γ ⊢ Δ)

  -- And Rules

  | andR : {Γ Δ : Multiset Formula}
         → {P Q : Formula}
         → Provable (Γ ⊢ P ::ₘ Δ)
         → Provable (Γ ⊢ Q ::ₘ Δ)
         → Provable (Γ ⊢ P ::ₘ Q ::ₘ Δ)

--   | andL : {Γ Δ : Multiset Formula}
--          → {P Q : Formula}
--          → Provable (P ::ₘ Q ::ₘ Γ ⊢ Δ)
--          → Provable ([Formula| P & Q]::ₘ Γ ⊢ Δ)

  -- Or Rules

  | orR : {Γ Δ : Multiset Formula}
        → {P Q : Formula}
        → Provable (Γ ⊢ P ::ₘ Q ::ₘ Δ)
        → Provable (Γ ⊢ Formula.or P Q ::ₘ Δ)

  | orL : {Γ Δ : Multiset Formula}
        → {P Q : Formula}
        → Provable (P ::ₘ Γ ⊢ Δ)
        → Provable (Q ::ₘ Γ ⊢ Δ)
        → Provable (Formula.or P Q ::ₘ Γ ⊢ Δ)

  -- Weakening Rules

  | weakL : {Γ Δ : Multiset Formula}
          → {Φ : Formula}
          → Provable (Γ ⊢ Δ)
          → Provable (Φ ::ₘ Γ ⊢ Δ)

  | weakR : {Γ Δ : Multiset Formula}
          → {Φ : Formula}
          → Provable (Γ ⊢ Δ)
          → Provable (Γ ⊢ Φ ::ₘ Δ)

  -- TODO Uniform Substituition
  | usubst : ∀ (Γ Δ : Multiset Formula),
             ⊥
           → Provable (Γ ⊢ Δ)

syntax "⌈" dL_formula,* " ⊢ " dL_formula,* "⌉" : term
macro_rules
  | `(⌈ ⊢ ⌉) => `(Sequent.mk ∅ ∅)
  | `(⌈ $[$p:dL_formula],* ⊢ ⌉) => `(Sequent.mk [$[[Formula|$p]],*] ∅)
  | `(⌈ ⊢ $q:dL_formula,* ⌉) => `(Sequent.mk ∅ [$[[Formula|$q]],*])
  | `(⌈ $[$p:dL_formula],* ⊢ $q:dL_formula,* ⌉) =>
      `(Sequent.mk [$[[Formula|$p]],*] [$[[Formula|$q]],*])

theorem dL_sound_complete (Γ Δ : Multiset Formula) : Provable (Γ ⊢ Δ) ↔ semantics Γ Δ := by
  sorry
