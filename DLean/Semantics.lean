import DLean.Syntax
import DLean.Interpretation
import DLean.State

def dynamicSemantics (i: Interpretation) (s : State) (t : Term) : ℝ :=
  match t with
    | Term.var  v         => s v
    | Term.neg  t         => - dynamicSemantics i s t
    | Term.plus x y       => dynamicSemantics i s x + dynamicSemantics i s y
    | Term.times x y      => dynamicSemantics i s x * dynamicSemantics i s y
    | Term.applyFn f args => let argValues := List.map (dynamicSemantics i s) args.toList;
                             i f argValues
    | Term.differential t => sorry
