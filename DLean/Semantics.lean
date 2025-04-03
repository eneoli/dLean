import Mathlib.Analysis.Calculus.Deriv.Basic

import DLean.Syntax
import DLean.Interpretation
import DLean.State

example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
  h.deriv

#check HMul

noncomputable def Term.dynamicSemantics (i: Interpretation) (s : State) (t : Term) : ℝ :=
  match t with
    | Term.var  v         => s v
    | Term.neg  t         => - dynamicSemantics i s t
    | Term.plus x y       => dynamicSemantics i s x + dynamicSemantics i s y
    | Term.times x y      => dynamicSemantics i s x * dynamicSemantics i s y
    | Term.applyFn f args => let argValues := .map (fun ⟨e, h⟩ => dynamicSemantics i s e) args.toVector.attach
                             i f argValues
    | Term.differential t => let fvars := t.freeAssignables
                             List.sum $ fvars.map (
                              fun x =>
                                s (Assignable.diff x) *
                                (deriv (fun y => dynamicSemantics i (fun x' => if x = x' then y else s x)) (s x)) t
                                -- (deriv (fun x => dynamicSemantics i (fun v => if true then 1 else s v) t) (s x'))
                             )
decreasing_by
  all_goals try decreasing_trivial
  have t : e ∈ args := (TermVector.mem_toVector_iff e args).mpr h
  have x : sizeOf e < sizeOf args := by
    apply TermVector.sizeOf_lt_of_mem t
  simp[*]
  omega
