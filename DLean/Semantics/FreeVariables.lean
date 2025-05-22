import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import DLean.Syntax

def Term.free_vars (t : Term) : Finset Assignable := match t with
  | .var a  => {a}
  | .neg t' => Term.free_vars t'
  | .plus t₁ t₂ => Term.free_vars t₁ ∪ Term.free_vars t₂
  | .times t₁ t₂ => Term.free_vars t₁ ∪ Term.free_vars t₂
  | .differential t => Term.free_vars t ∪ (List.map Assignable.diff ((Term.free_vars t).sort ((fun a b => a ≤ b)))).toFinset
  | .applyFn _ args => List.foldl (λa ⟨t, _⟩ => a ∪ Term.free_vars t) ∅ args.toList.attach
decreasing_by
  all_goals try decreasing_trivial
  have h := TermVector.toList_eq_size args
  decreasing_trivial
