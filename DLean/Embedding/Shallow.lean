import DLean.Syntax.Syntax
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics

open Semantics

def Formula.eval (i : Interpretation) (s : State) (Φ : Formula) : Prop := match Φ with
  | .True => _root_.True
  | .False => _root_.False
  | .and Φ₁ Φ₂ => Formula.eval i s Φ₁ ∧ Formula.eval i s Φ₂
  | .not Φ' => ¬Formula.eval i s Φ'
  | .forall x Φ' => ∀ (r : ℝ), Formula.eval i (s.update (Assignable.var x) r) Φ'
  | .exists x Φ' => ∃ (r : ℝ), Formula.eval i (s.update (Assignable.var x) r) Φ'
  | .box α Φ' => ∀ (s' : State), ⟨s, s'⟩ ∈ Program.denote i α → Formula.eval i s' Φ'
  | .diamond α Φ' => ∃ (s' : State), ⟨s, s'⟩ ∈ Program.denote i α → Formula.eval i s' Φ'
  | .eq t₁ t₂ => ∀ (i : Interpretation), Term.denote i s t₁ = Term.denote i s t₂
  | .gte t₁ t₂ => ∀ (i : Interpretation), Term.denote i s t₁ >= Term.denote i s t₂
  | .applyPred p args => ∀ (i : Interpretation), i (Symbol.Predicate p) $ args.toVector.map (Term.denote i s)
