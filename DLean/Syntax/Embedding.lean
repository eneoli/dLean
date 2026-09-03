import DLean.Syntax.Definitions
import Qq

open Lean Meta Qq

namespace Embedding

section SyntaxCategories

declare_syntax_cat dL_var        (behavior := symbol)
declare_syntax_cat dL_dot
declare_syntax_cat dL_term       (behavior := symbol)
declare_syntax_cat dL_formula    (behavior := symbol)
declare_syntax_cat dL_program    (behavior := symbol)
declare_syntax_cat dL_ode        (behavior := symbol)
declare_syntax_cat dL_ode_system (behavior := symbol)

scoped syntax:max ident : dL_var
scoped syntax:max dL_var "’" : dL_var

-- FIXME: We only support parsing for 0,1,2,3,4,5,6,7,8,9 but not more like ·₄₂ for now.
scoped syntax:max "·₀" : dL_dot
scoped syntax:max "·₁" : dL_dot
scoped syntax:max "·₂" : dL_dot
scoped syntax:max "·₃" : dL_dot
scoped syntax:max "·₄" : dL_dot
scoped syntax:max "·₅" : dL_dot
scoped syntax:max "·₆" : dL_dot
scoped syntax:max "·₇" : dL_dot
scoped syntax:max "·₈" : dL_dot
scoped syntax:max "·₉" : dL_dot

scoped syntax:max dL_var : dL_term
scoped syntax:max dL_dot : dL_term
scoped syntax:max num : dL_term
scoped syntax:max scientific : dL_term
scoped syntax:max "(" dL_term ")" : dL_term
scoped syntax:max "(" dL_term ")’" : dL_term
scoped syntax:max ident "(" dL_term,* ")" : dL_term
scoped syntax:max ident "(|" dL_var,* "|)" : dL_term
scoped syntax:30  " - " dL_term:30 : dL_term
scoped syntax:20  dL_term:20 " * " dL_term:21 : dL_term
scoped syntax:10  dL_term:10 " + " dL_term:11 : dL_term
scoped syntax:10  dL_term:10 " - " dL_term:11 : dL_term

scoped syntax:max "true" : dL_formula
scoped syntax:max "false" : dL_formula
scoped syntax:max ident : dL_formula
scoped syntax:max "(" dL_formula ")" : dL_formula
scoped syntax:max ident "(" dL_term,* ")" : dL_formula
scoped syntax:max ident "(|" dL_var,* "|)" : dL_formula
scoped syntax:max dL_term " = " dL_term : dL_formula
scoped syntax:max dL_term " ≥ " dL_term : dL_formula
scoped syntax:max dL_term " ≠ " dL_term : dL_formula
scoped syntax:max dL_term " > " dL_term : dL_formula
scoped syntax:max dL_term " < " dL_term : dL_formula
scoped syntax:max dL_term " ≤ " dL_term : dL_formula
scoped syntax:70  "¬" dL_formula:70 : dL_formula
scoped syntax:60  "∀" dL_var ", " dL_formula:60 : dL_formula
scoped syntax:60  "∃" dL_var ", " dL_formula:60 : dL_formula
scoped syntax:60  "[" dL_program "]" dL_formula:60 : dL_formula
scoped syntax:60  "⟨" dL_program "⟩" dL_formula:60 : dL_formula
scoped syntax:50 dL_program " ≼ " dL_program : dL_formula
scoped syntax:50 dL_program " ≃ " dL_program : dL_formula
scoped syntax:40  dL_formula:41 " ∧ " dL_formula:40 : dL_formula
scoped syntax:30  dL_formula:31 " ∨ " dL_formula:30 : dL_formula
scoped syntax:20  dL_formula:21 " → " dL_formula:20 : dL_formula
scoped syntax:10  dL_formula:11 " ↔ " dL_formula:11 : dL_formula

scoped syntax:40 (dL_var " = " dL_term) : dL_ode
scoped syntax:40 dL_ode,+ : dL_ode_system

scoped syntax:max ident : dL_program
scoped syntax:max " ( " dL_program " ) " : dL_program
scoped syntax:40 dL_var " := " dL_term : dL_program
scoped syntax:40 dL_var " :=*" : dL_program
scoped syntax:40 dL_ode_system (" & " dL_formula)? : dL_program
scoped syntax:30 "?" dL_formula:60 : dL_program
scoped syntax:30 dL_program:30 "* " : dL_program
scoped syntax:20 dL_program:21 " ; " dL_program:20 : dL_program
scoped syntax:10 dL_program:11 " ∪ " dL_program:10 : dL_program

end SyntaxCategories

section Elaborators

def parseBaseVariable (str : String) : MetaM Q(Variable) := do
  let ⟨pre, post⟩ := str.toList.span Char.isAlphanum
  if post.length > 0 then
    throwError "Variables can only contain alphanumeric chars."
  else
    let variableName : Q(String) := mkStrLit (String.ofList pre)
    pure q(Variable.base $variableName)

partial def elabVar : Syntax → MetaM Q(Variable)
  | `(dL_var| $var:ident) => do
    let varExpr : Q(Variable) ← parseBaseVariable var.getId.toString
    pure varExpr

  | `(dL_var| $var’) => do
    let varExpr ← elabVar var
    pure q(Variable.diff $varExpr)

  | _ => Lean.Elab.throwUnsupportedSyntax

partial def elabDot : Syntax → MetaM Q(ℕ)
  | `(dL_dot| ·₀) => pure q(0)
  | `(dL_dot| ·₁) => pure q(1)
  | `(dL_dot| ·₂) => pure q(2)
  | `(dL_dot| ·₃) => pure q(3)
  | `(dL_dot| ·₄) => pure q(4)
  | `(dL_dot| ·₅) => pure q(5)
  | `(dL_dot| ·₆) => pure q(6)
  | `(dL_dot| ·₇) => pure q(7)
  | `(dL_dot| ·₈) => pure q(8)
  | `(dL_dot| ·₉) => pure q(9)

  | _ => Lean.Elab.throwUnsupportedSyntax

partial def elabTerm : Syntax → MetaM Q(_root_.Term)
  | `(dL_term| $var:dL_var) => do
    let varExpr ← elabVar var
    pure q(_root_.Term.var $varExpr)

  | `(dL_term| $dot:dL_dot) => do
    let n ← elabDot dot
    pure q(_root_.Term.dot $n)

  | `(dL_term| $n:num) => do
    let nExpr : Q(ℕ) := mkNatLit (n.getNat)
    pure q(Term.applyFn (Fn.num $nExpr) TermVector.nil)

  | `(dL_term| $r:scientific) => do
    let (n, sign, e) := r.getScientific
    let nExpr : Q(ℕ) := mkNatLit n
    let eExpr : Q(ℕ) := mkNatLit e
    let eSign : Q(ℤ) := if sign then q(-$eExpr) else q($eExpr)
    pure q(Term.applyFn (Fn.num ($nExpr * 10 ^ $eSign)) TermVector.nil)

  | `(dL_term| - $t:dL_term) => do
    let tExpr ← elabTerm t
    pure q(Term.neg $tExpr)

  | `(dL_term| $t₁:dL_term + $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Term.plus $t₁Expr $t₂Expr)

  | `(dL_term| $t₁:dL_term - $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Term.minus $t₁Expr $t₂Expr)

  | `(dL_term| $t₁:dL_term * $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Term.times $t₁Expr $t₂Expr)

  | `(dL_term|$f:ident (|$[$args:dL_var],*|)) => do
    let vars ← args.mapM elabVar
    let taboo : Q(List Variable) := vars.foldr (fun v acc ↦ q(List.cons $v $acc)) q([])
    let FName : Q(String) := mkStrLit f.getId.toString
    let unitFun : Q(UnitFunctional) := q(UnitFunctional.mk $FName $taboo)
    pure q(Term.unit $unitFun)

  | `(dL_term|$f:ident ($args:dL_term,*)) => do
    let args : Array Syntax := args
    let fnName : Q(String) := mkStrLit f.getId.toString
    let fnArity : Q(ℕ) := mkNatLit args.size
    let fn : Q(Fn) := q(Fn.sym (FunctionSymbol.udef $fnName $fnArity))

    let argsExpr ← Array.mapM id <| (args.map elabTerm)
    let argsTermVectorExpr ← argsExpr.foldrM
      (fun e acc => mkAppM ``TermVector.cons #[e, acc])
      (.const ``TermVector.nil [])
    pure <| mkApp q(Term.applyFn $fn) argsTermVectorExpr

  | `(dL_term|( $t:dL_term )’) => do
    let tExpr ← elabTerm t
    pure q(Term.differential $tExpr)

  | `(dL_term|( $t:dL_term )) => elabTerm t

  | _ => Lean.Elab.throwUnsupportedSyntax

mutual
partial def elabFormula : Syntax → MetaM Q(Formula)
  | `(dL_formula| true) => pure q(Formula.True)

  | `(dL_formula| false) => pure q(Formula.False)

  | `(dL_formula| $P:ident) => pure <| Expr.const P.getId []

  | `(dL_formula| ¬$Φ:dL_formula) => do
    let e ← elabFormula Φ
    pure q(Formula.not $e)

  | `(dL_formula| $Φ₁:dL_formula ∧ $Φ₂:dL_formula) => do
    let Φ₁Expr ← elabFormula Φ₁
    let Φ₂Expr ← elabFormula Φ₂
    pure q(Formula.and $Φ₁Expr $Φ₂Expr)

  | `(dL_formula| ∀ $x:dL_var, $Φ:dL_formula) => do
    let varExpr ← elabVar x
    let ΦExpr ← elabFormula Φ
    pure q(Formula.forall $varExpr $ΦExpr)

  | `(dL_formula| ∃ $x:dL_var, $Φ:dL_formula) => do
    let varExpr ← elabVar x
    let ΦExpr ← elabFormula Φ
    pure q(Formula.exists $varExpr $ΦExpr)

  | `(dL_formula| [$α:dL_program]$Φ:dL_formula) => do
    let programExpr ← elabProgram α
    let formulaExpr ← elabFormula Φ
    pure q(Formula.box $programExpr $formulaExpr)

  | `(dL_formula| ⟨$α:dL_program⟩$Φ:dL_formula) => do
    let programExpr ← elabProgram α
    let formulaExpr ← elabFormula Φ
    pure q(Formula.diamond $programExpr $formulaExpr)

  | `(dL_formula|$f:ident (|$[$args:dL_var],*|)) => do
    let vars ← args.mapM elabVar
    let taboo : Q(List Variable) := vars.foldr (fun v acc ↦ q(List.cons $v $acc)) q([])
    let FName : Q(String) := mkStrLit f.getId.toString
    let unitPred : Q(UnitPredicational) := q(UnitPredicational.mk $FName $taboo)
    pure q(Formula.unit $unitPred)

  | `(dL_formula| $p:ident ($args:dL_term,*)) => do
    let args : Array Lean.Syntax := args
    let predSymName : Q(String) := mkStrLit p.getId.toString
    let predSymArity : Q(Nat) := mkNatLit args.size
    let predSym := q(PredicateSymbol.mk $predSymName $predSymArity)
    let argsExpr ← args.mapM elabTerm
    let argsTermVector ← argsExpr.foldrM
      (fun e acc => mkAppM `TermVector.cons #[e, acc]) q(TermVector.nil)
    pure <| mkApp q(Formula.applyPred $predSym) argsTermVector

  | `(dL_formula| $t₁:dL_term = $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Formula.eq $t₁Expr $t₂Expr)

  | `(dL_formula| $t₁:dL_term ≥ $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Formula.gte $t₁Expr $t₂Expr)

  | `(dL_formula| $Φ₁:dL_formula ∨ $Φ₂:dL_formula) => do
    let Φ₁Expr ← elabFormula Φ₁
    let Φ₂Expr ← elabFormula Φ₂
    pure q(Formula.or $Φ₁Expr $Φ₂Expr)

  | `(dL_formula| $Φ₁:dL_formula → $Φ₂:dL_formula) => do
    let Φ₁Expr ← elabFormula Φ₁
    let Φ₂Expr ← elabFormula Φ₂
    pure q(Formula.implies $Φ₁Expr $Φ₂Expr)

  | `(dL_formula| $Φ₁:dL_formula ↔ $Φ₂:dL_formula) => do
    let Φ₁Expr ← elabFormula Φ₁
    let Φ₂Expr ← elabFormula Φ₂
    pure q(Formula.equiv $Φ₁Expr $Φ₂Expr)

  | `(dL_formula| $t₁:dL_term ≠ $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Formula.neq $t₁Expr $t₂Expr)

  | `(dL_formula| $t₁:dL_term > $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Formula.gt $t₁Expr $t₂Expr)

  | `(dL_formula| $t₁:dL_term < $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Formula.lt $t₁Expr $t₂Expr)

  | `(dL_formula| $t₁:dL_term ≤ $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    pure q(Formula.lte $t₁Expr $t₂Expr)

  | `(dL_formula| ( $Φ:dL_formula )) => elabFormula Φ

  | `(dL_formula| $α₁:dL_program ≼ $α₂:dL_program) => do
    let α₁Expr ← elabProgram α₁
    let α₂Expr ← elabProgram α₂
    pure q(Formula.ref $α₁Expr $α₂Expr)

  | `(dL_formula| $α₁:dL_program ≃ $α₂:dL_program) => do
    let α₁Expr ← elabProgram α₁
    let α₂Expr ← elabProgram α₂
    pure q(Formula.progEquiv $α₁Expr $α₂Expr)

  | _ => Lean.Elab.throwUnsupportedSyntax

partial def elabProgram : Syntax → MetaM Q(Program)
  | `(dL_program|$sym:ident) => do
    let programSymbol : Q(String) := mkStrLit sym.getId.toString
    let programSymbolExpr := q(ProgramSymbol.mk $programSymbol)
    pure q(Program.const $programSymbolExpr)

  | `(dL_program| $name:dL_var := $t:dL_term) => do
    let var ← elabVar name
    let term ← elabTerm t
    pure q(Program.assign $var $term)

  | `(dL_program| $name:dL_var :=*) => do
    let var ← elabVar name
    pure q(Program.random $var)

  | `(dL_program| ?$Φ:dL_formula) => do
    let Φ ← elabFormula Φ
    pure q(Program.test $Φ)

  | `(dL_program| $[$v:dL_var’ = $t:dL_term],* $[& $ψ:dL_formula]?) => do
    let terms ← t.mapM elabTerm
    let assignables ← v.mapM elabVar
    let system := (Array.zipWith (fun a t => q(ODE.mk $a $t)) assignables terms).toList
    let systemExpr : Q(OdeSystem) := system.foldr (fun ode expr => q(List.cons $ode $expr)) q([])
    let constraint := (← ψ.mapM elabFormula).getD q(Formula.True)
    pure q(Program.ode $systemExpr $constraint)

  | `(dL_program| $_:dL_ode_system $[& $_:dL_formula]?) => do
    throwError "Left hand side of ODE should be a primed variable"

  | `(dL_program| $α:dL_program ∪ $β:dL_program) => do
    let αExpr ← elabProgram α
    let βExpr ← elabProgram β
    pure q(Program.choice $αExpr $βExpr)

  | `(dL_program| $α:dL_program ; $β:dL_program) => do
    let αExpr ← elabProgram α
    let βExpr ← elabProgram β
    pure q(Program.seq $αExpr $βExpr)

  | `(dL_program| $α:dL_program *) => do
    let α ← elabProgram α
    pure q(Program.loop $α)

  | `(dL_program| ( $α:dL_program )) => elabProgram α

  | _ => Lean.Elab.throwUnsupportedSyntax
end

scoped elab "[Var|" v:dL_var "]"         : term => elabVar v
scoped elab "[Dot|" t:dL_term "]"       : term => elabDot t
scoped elab "[Term|" t:dL_term "]"       : term => elabTerm t
scoped elab "[Formula|" Φ:dL_formula "]" : term => elabFormula Φ
scoped elab "[Program|" α:dL_program "]" : term => elabProgram α

end Elaborators

section Delaborators

open PrettyPrinter Delaborator SubExpr

/--
Extract the string of a symbol/variable to return an ident instead.
-/
def delabStructString (expr : Q(String)) : Delab := do
  let e ← reduce expr
  match e with
    | .lit lit => match lit with
      | .strVal s => return mkIdent <| Name.mkSimple <| s
      | _ => throwError "Exptected String Literal"
    | _ => failure

@[app_delab Variable.base]
def delabVariable.base : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Variable.base 1
  delab expr.appArg!

@[app_delab Variable.diff]
def delabAssignable.diff : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Variable.diff 1
  let a := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_var| $a’)⟩

section Delaborators.Term

partial def delabTaboo (expr : Expr) : DelabM (List (Lean.TSyntax `dL_var)) := do
  guard <| expr.isAppOfArity' ``List.nil 0 || expr.isAppOfArity' ``List.cons 3
  if expr.isAppOfArity' ``List.nil 0 then
    pure []
  else
    let tail := expr.appArg!
    let head := expr.appFn!.appArg!
    pure <| ⟨← delab head⟩ :: (← delabTaboo tail)

@[app_delab UnitFunctional.mk]
def delabUnitFunctional.mk : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``UnitFunctional.mk 2
  let F := ⟨← delabStructString expr.appFn!.appArg!⟩
  -- FIXME
  -- let taboo := ⟨← delabTaboo expr.appArg!⟩
  return ⟨← `(dL_term| $F:ident(||))⟩

@[app_delab Fn.num]
def delabFn.num : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Fn.num 1
  delab expr.appArg!

@[app_delab Fn.sym]
def delabFn.sym : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Fn.sym 1
  delab expr.appArg!

@[app_delab FunctionSymbol.udef]
def delabFunctionSymbol.udef : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``FunctionSymbol.udef 2
  delabStructString expr.appFn!.appArg!

partial def delabTermVector (expr : Expr) : DelabM (List (Lean.TSyntax `term)) := do
  guard <| expr.isAppOfArity' ``TermVector.nil 0 || expr.isAppOfArity' ``TermVector.cons 3
  if expr.isAppOfArity' ``TermVector.nil 0 then
    pure []
  else
    let tail := expr.appArg!
    let head := expr.appFn!.appArg!
    pure <| (← delab head) :: (← delabTermVector tail)

-- TODO unbox

@[app_delab Term.var]
def delabTerm.var : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.var 1
  let name := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_term| $name)⟩

@[app_delab Term.neg]
def delabTerm.neg : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.neg 1
  let t ← withAppArg delab
  `(-$t)

@[app_delab Term.plus]
def delabTerm.plus : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.plus 2
  let t₁ ← withNaryArg 0 delab
  let t₂ ← withNaryArg 1 delab
  `($t₁ + $t₂)

@[app_delab Term.times]
def delabTerm.times : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.times 2
  let t₁ ← withNaryArg 0 delab
  let t₂ ← withNaryArg 1 delab
  `($t₁ * $t₂)

@[app_delab Term.unit]
def delabTerm.unit : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.unit 1
  let F ← withAppArg delab
  `($F)

-- TODO use dL_term category, adjust delabTermVector
@[app_delab Term.applyFn]
def delabTerm.applyFn : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.applyFn 2
  let f ← delab expr.appFn!.appArg!
  let args := (← delabTermVector expr.appArg!).toArray

  if args.size == 0 then
    `($f ())
  else if args.size == 1 then
    let a := args[0]!
    `($f ($a))
  else
    let a := args[0]!
    let as := args[1:].toArray
    `($f ($a, $[$as],*))

@[app_delab Term.differential]
def delabTerm.differential : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.differential 1
  let t := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_term| ($t)’)⟩

end Delaborators.Term

section Delaborators.Program

@[app_delab ProgramSymbol.mk]
def delabProgramSymbol.mk : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``ProgramSymbol.mk 1
  delabStructString expr.appArg!

@[app_delab Program.const]
def delabConst : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.const 1
  let p := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_program| $p)⟩

@[app_delab Program.test]
def delabTest : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.test 1
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| ? $Φ)⟩

@[app_delab Program.assign]
def delabAssign : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.assign 2
  let assignable := ⟨← delab expr.appFn!.appArg!⟩
  let t := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $assignable:dL_var := $t)⟩

@[app_delab Program.random]
def delabRandom : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.random 1
  let assignable := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $assignable:dL_var :=*)⟩

@[app_delab Program.seq]
def delabSequence : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.seq 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $α₁ ; $α₂)⟩

@[app_delab Program.choice]
def delabChoice : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.choice 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $α₁ ∪ $α₂)⟩

@[app_delab Program.loop]
def delabLoop : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.loop 1
  let α := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $α*)⟩

@[app_delab ODE.mk]
def delabOde : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``ODE.mk 2
  let var  := ⟨← delab expr.appFn!.appArg!⟩
  let term := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_ode| $var:dL_var’ = $term)⟩

partial def delabOdeSystem : DelabM (Array (TSyntax `dL_ode)) := do
  let system ← getExpr
  guard <| (system.isAppOfArity' ``List.nil 1) || (system.isAppOfArity ``List.cons 3)

  if system.isAppOfArity' ``List.nil 1 then
    pure #[]
  else
    withAppArg do
    let head := ⟨← delab system.appFn!.appArg!⟩
    let tail ← delabOdeSystem
    pure (head :: tail.toList).toArray

@[app_delab Program.ode]
def delabODE : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.ode 2
  let Ψ := ⟨← delab expr.appArg!⟩

  withAppFn do
  withAppArg do
  let system ← delabOdeSystem
  return ⟨← `(dL_program| $[$system:dL_ode],* & $Ψ:dL_formula)⟩

end Delaborators.Program

section Delaborators.Formula

@[app_delab Formula.True]
def delabTrue : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.True 0
  return ⟨← `(dL_formula| true)⟩

@[app_delab Formula.False]
def delabFalse : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.False 0
  return ⟨← `(dL_formula| false)⟩

@[app_delab Formula.and]
def delabAnd : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.and 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ ∧ $Φ₂)⟩


@[app_delab UnitPredicational.mk]
def delabUnitPredicational.mk : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``UnitPredicational.mk 2
  let P := ⟨← delabStructString expr.appFn!.appArg!⟩
  -- FIXME
  -- let taboo := ⟨← delabTaboo expr.appArg!⟩
  return ⟨← `(dL_term| $P:ident(||))⟩

@[app_delab Formula.unit]
def delabFormula.unit : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.unit 1
  let P ← withAppArg delab
  `($P)

@[app_delab PredicateSymbol.mk]
def delabPredicateSymbol.mk : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``PredicateSymbol.mk 2
  delabStructString expr.appFn!.appArg!


@[app_delab Formula.applyPred]
def delabApplyPred : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.applyPred 2
  let args := (← delabTermVector expr.appArg!).toArray
  let p := (← delab expr.appFn!.appArg!)
  if args.size == 0 then
    `($p)
  else if args.size == 1 then
    let a := args[0]!
    `($p ($a))
  else
    let a := args[0]!
    let as := args[1:].toArray
    `($p ($a, $[$as],*))

def delabInEquality (ctor : Name) (fn : Lean.Term → Lean.Term → Delab) : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ctor 2
  let t₁ := ⟨← delab expr.appFn!.appArg!⟩
  let t₂ := ⟨← delab expr.appArg!⟩
  return ⟨← fn t₁ t₂⟩

@[app_delab Formula.eq]
def delabEq : Delab := delabInEquality ``Formula.eq (fun t₁ t₂ => `($t₁ = $t₂))

@[app_delab Formula.gte]
def delabGte : Delab := delabInEquality ``Formula.gte (fun t₁ t₂ => `($t₁ ≥ $t₂))

@[app_delab Formula.not]
def delabNot : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.not 1
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ¬$Φ)⟩

@[app_delab Formula.or]
def delabOr : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.or 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ ∨ $Φ₂)⟩

@[app_delab Formula.forall]
def delabForall : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.forall 2
  let x := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ∀$x, $Φ)⟩

@[app_delab Formula.exists]
def delabExists : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.exists 2
  let x := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ∃$x, $Φ)⟩

@[app_delab Formula.box]
def delabBox : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.box 2
  let α := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| [$α]$Φ)⟩

@[app_delab Formula.diamond]
def delabDiamond : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.diamond 2
  let α := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ⟨$α⟩$Φ)⟩

@[app_delab Formula.implies]
def delabImplies : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.implies 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ → $Φ₂)⟩

@[app_delab Formula.equiv]
def delabEquiv : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.equiv 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ ↔ $Φ₂)⟩

@[app_delab Formula.neq]
def delabNeq : Delab := delabInEquality ``Formula.neq (fun t₁ t₂ => `($t₁ ≠ $t₂))

@[app_delab Formula.gt]
def delabGt : Delab := delabInEquality ``Formula.gt (fun t₁ t₂ => `($t₁ > $t₂))

@[app_delab Formula.lt]
def delabLt : Delab := delabInEquality ``Formula.lt (fun t₁ t₂ => `($t₁ < $t₂))

@[app_delab Formula.lte]
def delabLte : Delab := delabInEquality ``Formula.lte (fun t₁ t₂ => `($t₁ ≤ $t₂))

@[app_delab Formula.ref]
def delabRef : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.ref 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_formula| $α₁:dL_program ≼ $α₂:dL_program)⟩

@[app_delab Formula.progEquiv]
def delabProgEquiv : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.progEquiv 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_formula| $α₁:dL_program ≃ $α₂:dL_program)⟩

end Delaborators.Formula

end Delaborators

end Embedding
