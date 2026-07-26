import DLean.Syntax.Syntax
import DLean.Semantics.DynamicSemantics

import DLean.Embedding.Shallow

open Semantics
open Embedding

def sound (φ : Formula) : Prop := ∀ (i: Interpretation) (s : State), s ∈ φ.denote i

syntax "⌈" dL_formula "⌉" : term
macro_rules
  | `(⌈ $q:dL_formula ⌉) => `(sound [Formula|$q])

/-- `P` is a substitute for a predicational, i.e. `k` can be uniformly substituted by any `?φ`. -/
-- ⟨?φ⟩ true
-- ¬ [?φ] false
-- ¬ (φ → False)
-- ¬ (¬ φ ∨ False)
-- φ ∧ True
-- φ
def P := [Formula|⟨k⟩true]
def Q := [Formula|⟨l⟩true]


/- Relate the substituted program by the predicate -/
lemma pred : sound [Formula| ⟨?p()⟩true ↔ p()] := by
  unfold sound
  intros i s
  simpFormula
  simp[Formula.denote, Program.denote_test]
