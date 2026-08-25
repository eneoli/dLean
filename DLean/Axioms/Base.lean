import DLean.Syntax.Syntax
import DLean.Semantics.DynamicSemantics

import DLean.Embedding.Shallow

open Semantics
open Embedding

def sound (φ : Formula) : Prop := ∀ (i: Interpretation) (s : State), s ∈ φ.denote i

syntax "⌈" dL_formula "⌉" : term
macro_rules
  | `(⌈ $q:dL_formula ⌉) => `(sound [Formula|$q])
