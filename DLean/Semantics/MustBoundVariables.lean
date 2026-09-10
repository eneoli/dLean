import DLean.Syntax.Basic
import DLean.Semantics.BoundVariables
import DLean.Util.FCSet

def Program.mustBoundVars (α : Program) : Set Variable := match α with
  | .assign _ _
  | .random _
  | .test _
  | .ode _ _    => Program.boundVars α
  | .choice α β => Program.mustBoundVars α ∩ Program.mustBoundVars β
  | .seq α β    => Program.mustBoundVars α ∪ Program.mustBoundVars β
  | .const _
  | .loop _     => ∅

/-- Decidable version. -/
def Program.mustBoundVars' (α : Program) : FCSet Variable := match α with
  | .assign _ _
  | .random _
  | .test _
  | .ode _ _    => Program.boundVars' α
  | .choice α β => Program.mustBoundVars' α ∩ Program.mustBoundVars' β
  | .seq α β    => Program.mustBoundVars' α ∪ Program.mustBoundVars' β
  | .const _
  | .loop _     => ∅

theorem Program.must_bound_vars_decidable (α : Program)
  : Program.mustBoundVars α = Program.mustBoundVars' α := by
  match α with
    | .assign x t
    | .random x
    | .test Φ
    | .ode system Ψ =>
      simp[Program.mustBoundVars, Program.mustBoundVars']
      apply Program.bound_vars_decidable
    | .choice α β
    | .seq α β =>
      simp[Program.mustBoundVars, Program.mustBoundVars']
      rw[Program.must_bound_vars_decidable α]
      rw[Program.must_bound_vars_decidable β]
    | .const _
    | .loop _  =>
      simp[Program.mustBoundVars, Program.mustBoundVars']
