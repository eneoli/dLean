import DLean.Syntax.Syntax
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics

import DLean.Embedding.Shallow

import DLean.Axioms.Base

open Semantics
open Embedding

theorem DW : sound [Formula| [x’ = f(x) & q(x)]q(x)]  := by
  intros i s
  simp[Formula.denote, setOf]
  unfold Program.denote
  simp
  simp[odeEvolutionFormula, Formula.denote]
  simp[Membership.mem, Set.Mem]
  intros w r Hr φ Hstart Hend Hinv
  have ⟨⟨left,H⟩, right⟩ := Hinv r ?goal (by simp)
  . clear left right
    revert H
    simp[TermVector.toVector]
    simp[Term.denote]
    simp[Hend]
  . trivial
