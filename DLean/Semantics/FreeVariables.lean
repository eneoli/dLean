import Mathlib.Data.Finset.Basic
import DLean.Syntax.Syntax

def Term.freeVars : (t : Term) → Finset Assignable
  | Term.var  v         => {v}
  | Term.neg  t'        => Term.freeVars t'
  | Term.plus  t₁ t₂
  | Term.times t₁ t₂    => Term.freeVars t₁ ∪ Term.freeVars t₂
  | Term.differential t => let vs := Term.freeVars t;
                            vs ∪ Finset.map Assignable.diff_emb vs
  | Term.applyFn _ ts   =>  List.foldl (λ acc ⟨t, _⟩ => acc ∪ Term.freeVars t) ∅ ts.toList.attach
decreasing_by
  all_goals try decreasing_trivial
  have h := TermVector.toList_eq_size ts
  decreasing_trivial
