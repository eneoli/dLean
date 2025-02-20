import DLean.Syntax
import DLean.State

def dynamicSemantics (s : State) (t : Term) : ℝ :=
  match t with
    | Term.real r           => r
    | Term.var  v           => s v
    | Term.neg  t           => - dynamicSemantics s t
    | Term.plus x y         => dynamicSemantics s x + dynamicSemantics s y
    | Term.minus x y        => dynamicSemantics s x - dynamicSemantics s y
    | Term.times x y        => dynamicSemantics s x * dynamicSemantics s y
    | Term.applyFn f n args => sorry
    | Term.differential t   => sorry
