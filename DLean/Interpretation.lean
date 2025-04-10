import DLean.Syntax
import DLean.State

inductive Symbol where
  | PredicateSymbol : PredicateSymbol → Symbol
  | FunctionSymbol  : FunctionSymbol → Symbol
  | ProgramSymbol   : ProgramSymbol  → Symbol

def Interpretation.ReturnType : (symbol : Symbol) → Type
  | Symbol.PredicateSymbol p => Vector ℝ p.arity → Prop
  | Symbol.FunctionSymbol f  => Vector ℝ f.arity → ℝ
  | Symbol.ProgramSymbol _   => State × State → Prop

def Interpretation : Type := (s : Symbol) → Interpretation.ReturnType s
