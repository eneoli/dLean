import DLean.Syntax
import DLean.State
import DLean.DynamicSemantics

def Formula.eval (Φ : Formula) (s : State) : Prop := match Φ with
  | .True => true
  | .False => false
  | .and Φ₁ Φ₂ => Formula.eval Φ₁ s ∧ Formula.eval Φ₂ s
  | .not Φ' => ¬Formula.eval Φ' s
  | .forall x Φ' => ∀ (r : ℝ), Formula.eval Φ' $ s.update (Assignable.var x) r
  | .exists x Φ' => ∃ (r : ℝ), Formula.eval Φ' $ s.update (Assignable.var x) r
  | .box α Φ' => ∀ (i : Interpretation) (s' : State), ⟨s, s'⟩ ∈ Program.denote i α → Formula.eval Φ' s'
  | .diamond α Φ' => ∀ (i : Interpretation), ∃ (s' : State), ⟨s, s'⟩ ∈ Program.denote i α → Formula.eval Φ' s'
  | .eq t₁ t₂ => ∀ (i : Interpretation), Term.denote i s t₁ = Term.denote i s t₂
  | .gte t₁ t₂ => ∀ (i : Interpretation), Term.denote i s t₁ >= Term.denote i s t₂
  | .applyPred p args => ∀ (i : Interpretation), i (Symbol.Predicate p) $ args.toVector.map (Term.denote i s)

def Entails (Γ : List Formula) (Q : Formula) : Prop :=
  ∀ (s : State), Γ.foldl (λ acc Φ => acc ∧ Formula.eval Φ s) True → Formula.eval Q s

syntax:25 term:29 " ⊢ " term:25 : term
macro_rules
  | `($P:term ⊢ $Q:term) => `((Entails [$P] $Q))

@[app_unexpander Entails]
def unexpandEntails : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $Q) => `($Γ ⊢ $Q)
  | _ => throw ()

theorem foo : Formula.True ⊢ Formula.True := by
  