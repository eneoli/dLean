import DLean.Syntax
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.FreeVariables

open Semantics

lemma Term.coincidence (t : Term)
                       (i : Interpretation)
                       (j : Interpretation)
                       (v : State)
                       (w : State)
                       : State.isEqOn v w t.free_vars ∧
                         Interpretation.isEqOn i j t.signature → t.denote i v = t.denote i w := by
  sorry
