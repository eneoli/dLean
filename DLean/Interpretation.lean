import DLean.Syntax

def Interpretation : Type := (f: FunctionSymbol) → (Vector ℝ f.arity → ℝ)
