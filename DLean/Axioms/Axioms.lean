import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import DLean.Syntax.Syntax
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics

open Semantics

def sound (φ : Formula) : Prop := ∀(i: Interpretation), ∀(s : State), φ.denote i s

def const' : sound [Formula| (f())' = 0] := by
  sorry

def var' : sound [Formula| (x)' = x'] := by
  sorry

#print var'

def sum' : sound [Formula| (f(x) + g(x))' = (f(x))' + (g(x))'] := by
  unfold sound Formula.denote
  intros i s
  simp[setOf]
  simp[Term.denote]
  simp[Term.freeAssignables, TermVector.toList]
  simp[TermVector.toVector, Vector.append]
  simp[Term.denote]
  rw[deriv_add]
  . simp[mul_add] -- linarith
  . sorry
  . sorry

def assign : sound [Formula| [x:=f()]p(x) ↔ p(f())] := by
  sorry

def dW : sound [Formula| [x'=f(x)&q(x)]q(x)] := by
  intros i s
  simp[Formula.denote, setOf]
  unfold Program.denote
  simp
  simp[Program.denote.buildOdeFormula, Formula.denote]
  simp[Membership.mem, Set.Mem]
  simp[setOf]
  intros w r Hr φ Hstart Hend Hinv
  have ⟨⟨left,H⟩, right⟩ := Hinv r ?goal (by simp)
  . clear left right
    revert H
    simp[TermVector.toVector, Vector.append]
    simp[Term.denote]
    specialize Hend (Assignable.var (Variable.variable "x"))
    simp[Hend]
  . trivial
