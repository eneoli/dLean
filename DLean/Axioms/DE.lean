import DLean.Syntax.Syntax
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics

import DLean.Embedding.Shallow

import DLean.Axioms.Base

open Semantics
open Embedding

theorem DE : sound [Formula| [x’ = F(||) & Q(||)]P(||) ↔ [x’ = F(||) & Q(||)][x’ := F(||)]P(||)] := by
  intros i s
  simpFormula
  apply Iff.intro
  .
    intros h₁
    simp_all[Formula.denote]

    intros t h₂ u h₃
    apply h₁
    simp [Program.denote] at *

    let ⟨r, hr, φ, hp⟩:= h₂

    apply Exists.intro r
    and_intros
    . grind
    .
      apply Exists.intro φ
      and_intros
      . grind
      .
        rw[h₃]
        rw[hp.2.1]
        simp[Term.denote]
        simp[odeEvolutionFormula, Formula.denote_and] at hp
        simp[Formula.denote, Term.denote] at hp

        funext x

        grind
      . grind
  .
    intros h₁
    simp_all[Formula.denote]

    intros t h₂
    apply h₁
    . exact h₂
    .
      simp[Program.denote, Term.denote]
      simp[Program.denote, odeEvolutionFormula, Formula.denote_and] at h₂

      let ⟨r, hr, φ, hp⟩:= h₂

      rw[hp.2.1]

      simp[Formula.denote, Term.denote] at hp


      funext x
      grind
