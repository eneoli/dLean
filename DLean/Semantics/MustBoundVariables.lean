import DLean.Syntax.Syntax
import DLean.Semantics.BoundVariables

def Program.mustBoundVars (α : Program) : Set Assignable := match α with
  | .assign _ _
  | .test _
  | .ode _ _    => Program.boundVars α
  | .choice α β => Program.mustBoundVars α ∩ Program.mustBoundVars β
  | .seq α β    => Program.mustBoundVars α ∪ Program.mustBoundVars β
  | .const _
  | .loop _     => ∅
