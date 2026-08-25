import DLean.Syntax.Syntax
import DLean.Util.FCSet

def Program.boundVars (α : Program) : Set Assignable := match α with
  | .const _      => .univ
  | .assign x _
  | .random x     => {x}
  | .test _       => ∅
  | .seq α β
  | .choice α β   => Program.boundVars α ∪ Program.boundVars β
  | .loop α       => Program.boundVars α
  | .ode system _ => let fvars  := system.assignables
                     let fvars' := system.assignables.map Assignable.diff_emb
                     fvars ∪ fvars'

/-- Decidable version. -/
def Program.boundVars' (α : Program) : FCSet Assignable := match α with
  | .const _      => .univ
  | .assign x _
  | .random x     => {x}
  | .test _       => ∅
  | .seq α β
  | .choice α β   => Program.boundVars' α ∪ Program.boundVars' β
  | .loop α       => Program.boundVars' α
  | .ode system _ => let fvars  := system.assignables |> .Finite
                     let fvars' := system.assignables.map Assignable.diff_emb |> .Finite
                     fvars ∪ fvars'

section Theorems

theorem Program.bound_vars_decidable (α : Program)
  : Program.boundVars α = Program.boundVars' α := by
  match α with
  | .const _
  | .assign _ _
  | .random _
  | .test _     =>
    simp[Program.boundVars, Program.boundVars']
  | .seq α β
  | .choice α β =>
    simp[Program.boundVars, Program.boundVars']
    rw[Program.bound_vars_decidable α]
    rw[Program.bound_vars_decidable β]
  | .loop α       =>
    apply Program.bound_vars_decidable α
  | .ode system _ =>
    simp[Program.boundVars, Program.boundVars']

end Theorems
