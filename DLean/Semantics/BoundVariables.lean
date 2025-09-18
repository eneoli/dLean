import DLean.Syntax.Syntax

mutual

def Formula.boundVars (Φ : Formula) : Set Assignable := match Φ with
  | .True
  | .False
  | .eq _ _
  | .gte _ _
  | .applyPred _ _ => ∅
  | .not Φ'        => Formula.boundVars Φ'
  | .and Φ₁ Φ₂     => Formula.boundVars Φ₁ ∪ Formula.boundVars Φ₂
  | .forall x Φ
  | .exists x Φ    => {Assignable.var x} ∪ Formula.boundVars Φ
  | .box α Φ
  | .diamond α Φ   => Program.boundVars α ∪ Formula.boundVars Φ
  | .ref α β       => Program.boundVars α ∪ Program.boundVars β


def Program.boundVars (α : Program) : Set Assignable := match α with
  | .const _      => Assignable.Set
  | .assign x _   => {x}
  | .test _       => ∅
  | .seq α β
  | .choice α β   => Program.boundVars α ∪ Program.boundVars β
  | .loop α       => Program.boundVars α
  | .ode system _ => let fvars  := system.assignables
                     let fvars' := system.assignables.map Assignable.diff_emb
                     fvars ∪ fvars'

end
