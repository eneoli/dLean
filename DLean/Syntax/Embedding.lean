import DLean.Syntax.Definitions
import Qq

open Lean Meta Qq

namespace Embedding

section SyntaxCategories

declare_syntax_cat dL_term       (behavior := symbol)
declare_syntax_cat dL_formula    (behavior := symbol)
declare_syntax_cat dL_program    (behavior := symbol)
declare_syntax_cat dL_ode        (behavior := symbol)
declare_syntax_cat dL_ode_system (behavior := symbol)

scoped syntax:max ident : dL_term
scoped syntax:max num : dL_term
scoped syntax:max scientific : dL_term
scoped syntax:max "(" dL_term ")" : dL_term
scoped syntax:max "(" dL_term ")'" : dL_term
scoped syntax:max ident "(" dL_term,* ")" : dL_term
scoped syntax:30  " - " dL_term:30 : dL_term
scoped syntax:20  dL_term:20 " * " dL_term:21 : dL_term
scoped syntax:10  dL_term:10 " + " dL_term:11 : dL_term
scoped syntax:10  dL_term:10 " - " dL_term:11 : dL_term

scoped syntax:max "true" : dL_formula
scoped syntax:max "false" : dL_formula
scoped syntax:max ident : dL_formula
scoped syntax:max "(" dL_formula ")" : dL_formula
scoped syntax:max ident "(" dL_term,* ")" : dL_formula
scoped syntax:max dL_term " = " dL_term : dL_formula
scoped syntax:max dL_term " ≥ " dL_term : dL_formula
scoped syntax:max dL_term " ≠ " dL_term : dL_formula
scoped syntax:max dL_term " > " dL_term : dL_formula
scoped syntax:max dL_term " < " dL_term : dL_formula
scoped syntax:max dL_term " ≤ " dL_term : dL_formula
scoped syntax:70  "¬" dL_formula:70 : dL_formula
scoped syntax:60  "∀" ident ", " dL_formula:60 : dL_formula
scoped syntax:60  "∃" ident ", " dL_formula:60 : dL_formula
scoped syntax:60  "[" dL_program "]" dL_formula:60 : dL_formula
scoped syntax:60  "⟨" dL_program "⟩" dL_formula:60 : dL_formula
scoped syntax:50 dL_program " ≼ " dL_program : dL_formula
scoped syntax:50 dL_program " ≃ " dL_program : dL_formula
scoped syntax:40  dL_formula:41 " ∧ " dL_formula:40 : dL_formula
scoped syntax:30  dL_formula:31 " ∨ " dL_formula:30 : dL_formula
scoped syntax:20  dL_formula:21 " → " dL_formula:20 : dL_formula
scoped syntax:10  dL_formula:11 " ↔ " dL_formula:11 : dL_formula

scoped syntax:40 (ident " = " dL_term) : dL_ode
scoped syntax:40 dL_ode,+ : dL_ode_system

scoped syntax:max ident : dL_program
scoped syntax:max " ( " dL_program " ) " : dL_program
scoped syntax:40 ident " := " dL_term : dL_program
scoped syntax:40 dL_ode_system (" & " dL_formula)? : dL_program
scoped syntax:30 "?" dL_formula:60 : dL_program
scoped syntax:30 dL_program:30 "* " : dL_program
scoped syntax:20 dL_program:21 " ; " dL_program:20 : dL_program
scoped syntax:10 dL_program:11 " ∪ " dL_program:10 : dL_program

end SyntaxCategories

section Elaborators

def parseVariable (str : String) : MetaM Q(Variable) := do
  let ⟨pre, post⟩ := str.toList.span Char.isAlphanum
  if post.length > 0 then
    throwError "Variables can only contain alphanumeric chars."
  else
    let variableName : Q(String) := mkStrLit pre.asString
    pure q(Variable.mk $variableName)

inductive parseAssignable.Constraint : Type where
  | END_ARBITRARY
  | END_WITH_PRIME
  | END_WITH_PRIME_EX
  | END_WITH_NO_PRIME_ASSIGNABLE
deriving DecidableEq

def parseAssignable (c : parseAssignable.Constraint) (str : String) : MetaM Q(Assignable) := do
  let ⟨pre, post⟩ := str.toList.span Char.isAlphanum
  if pre.length == 0 then
    throwError "Assignables need to start with an alphanumeric part."
  else if not <| post.all (BEq.beq '\'') then
    throwError "Assignables can only end with alphanumeric chars or primes."
  else if (c = .END_WITH_PRIME || c = .END_WITH_PRIME_EX) && post.isEmpty then
    throwError "Expected primed identifier."
  else if (c = .END_WITH_NO_PRIME_ASSIGNABLE) && not post.isEmpty then
    throwError "Expected not primed identifier."
  else
    let variableName : Q(String) := mkStrLit pre.asString
    let baseAssignableExpr := q(Assignable.var (Variable.mk $variableName))
    let numPrimes := if c == .END_WITH_PRIME_EX then post.tail else post
    pure <| List.foldl (fun e _ => q(Assignable.diff $e)) baseAssignableExpr numPrimes

partial def elabTerm : Syntax → MetaM Q(_root_.Term)
  | `(dL_term| $var:ident) => do
    let assignableExpr ← parseAssignable .END_ARBITRARY var.getId.toString
    mkAppM ``Term.var #[assignableExpr]

  | `(dL_term| $n:num) => do
    let fn ← mkAppM ``Fn.num #[← mkAppM ``Number.mk #[
      mkNatLit n.getNat,
      mkNatLit 0,
      Expr.const ``Bool.false [],
    ]]
    mkAppM ``Term.applyFn #[fn, .const ``TermVector.nil []]

  | `(dL_term| $r:scientific) => do
    let (n, sign, e) := r.getScientific
    let fn ← mkAppM ``Fn.num #[← mkAppM ``Number.mk #[
      mkNatLit n,
      mkNatLit e,
      if sign then .const ``Bool.false [] else .const ``Bool.true [],
    ]]
    mkAppM ``Term.applyFn #[fn, .const ``TermVector.nil []]

  | `(dL_term| - $t:dL_term) => do mkAppM ``Term.neg #[← elabTerm t]

  | `(dL_term| $t₁:dL_term + $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    mkAppM ``Term.plus #[t₁Expr, t₂Expr]

  | `(dL_term| $t₁:dL_term - $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    mkAppM ``Term.minus #[t₁Expr, t₂Expr]

  | `(dL_term| $t₁:dL_term * $t₂:dL_term) => do
    let t₁Expr ← elabTerm t₁
    let t₂Expr ← elabTerm t₂
    mkAppM ``Term.times #[t₁Expr, t₂Expr]

  | `(dL_term|$f:ident ($args:dL_term,*)) => do
    let args : Array Syntax := args
    let fn ← mkAppM ``Fn.sym #[← mkAppM ``FunctionSymbol.udef #[
      Lean.mkStrLit f.getId.toString,
      Lean.mkNatLit args.size,
    ]]
    let argsExpr ← Array.mapM id <| (args.map elabTerm)
    let argsTermVectorExpr ← argsExpr.foldrM
      (fun e acc => mkAppM ``TermVector.cons #[e, acc])
      (.const ``TermVector.nil [])
    mkAppM ``Term.applyFn <| #[fn, argsTermVectorExpr]

  | `(dL_term|( $t:dL_term )') => do mkAppM ``Term.differential #[← elabTerm t]

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

  | `(dL_formula| ∀ $x:ident, $Φ:dL_formula) => do
    let assignableExpr ← parseVariable x.getId.toString
    let ΦExpr ← elabFormula Φ
    pure q(Formula.forall $assignableExpr $ΦExpr)

  | `(dL_formula| ∃ $x:ident, $Φ:dL_formula) => do
    let assignableExpr ← parseVariable x.getId.toString
    let ΦExpr ← elabFormula Φ
    pure q(Formula.exists $assignableExpr $ΦExpr)

  | `(dL_formula| [$α:dL_program]$Φ:dL_formula) => do
    let programExpr ← elabProgram α
    let formulaExpr ← elabFormula Φ
    pure q(Formula.box $programExpr $formulaExpr)

  | `(dL_formula| ⟨$α:dL_program⟩$Φ:dL_formula) => do
    let programExpr ← elabProgram α
    let formulaExpr ← elabFormula Φ
    pure q(Formula.diamond $programExpr $formulaExpr)

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

  | `(dL_program| $name:ident := $t:dL_term) => do
    let var ← parseAssignable .END_ARBITRARY name.getId.toString
    let term ← elabTerm t
    pure q(Program.assign $var $term)

  | `(dL_program| ?$Φ:dL_formula) => do
    let Φ ← elabFormula Φ
    pure q(Program.test $Φ)

  | `(dL_program| $[$v:ident = $t:dL_term],* $[& $ψ:dL_formula]?) => do
    let assignables ←
      v.mapM (parseAssignable .END_WITH_PRIME_EX ∘ Lean.Name.toString ∘ Lean.TSyntax.getId)
    let terms ← t.mapM elabTerm
    let system := (Array.zipWith (fun a t => q(ODE.mk $a $t)) assignables terms).toList
    let systemExpr : Q(OdeSystem) := system.foldr (fun ode expr => q(List.cons $ode $expr)) q([])
    let constraint := (← ψ.mapM elabFormula).getD q(Formula.True)
    pure q(Program.ode $systemExpr $constraint)

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

scoped elab "[Term|" t:dL_term "]"       : term => elabTerm t
scoped elab "[Formula|" Φ:dL_formula "]" : term => elabFormula Φ
scoped elab "[Program|" α:dL_program "]" : term => elabProgram α

end Elaborators

section Delaborators

open PrettyPrinter Delaborator SubExpr

def extractString (expr : Q(String)) : MetaM String := do
  let e ← reduce expr
  match e with
    | .lit lit => match lit with
      | .strVal s => pure s
      | _ => throwError "Exptected String Literal"
    | _ => throwError "Expected Literal Expression"

def extractNat (expr : Q(ℕ)) : MetaM ℕ := do
  let e ← reduce expr
  match e with
    | .lit lit => match lit with
      | .natVal n => pure n
      | _ => throwError "Exptected Nat Literal"
    | _ => throwError "Expected Literal Expression"

def extractBool (expr : Q(Bool)) : DelabM Bool := do
  let e : Q(Bool) ← reduce expr
  match e with
    | ~q(true) => pure true
    | ~q(false) => pure false
    | _ => throwError "Expected Boolean Expression Constant"

@[scoped delab app.Variable.mk]
def delabVariable.mk : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Variable.mk 1
  let ident := mkIdent <| Name.mkSimple <| (← extractString expr.appArg!)
  return ident

@[scoped delab app.Assignable.var]
def delabAssignable.var : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Assignable.var 1
  delab expr.appArg!

def delabVariableH (expr : Expr) : DelabM String := do
  guard <| expr.isAppOfArity' ``Variable.mk 1
  let ident := expr.appArg!
  match ident with
    | Expr.lit lit => match lit with
      | .strVal s => pure s
      | _ => unreachable!
    | _ => unreachable!

partial def delabAssignableH (expr : Expr) : DelabM String := do
  guard <| (expr.isAppOfArity' ``Assignable.var 1 || expr.isAppOfArity' ``Assignable.diff 1)
  if expr.isAppOfArity' ``Assignable.var 1 then
    delabVariableH expr.appArg!
  else
    pure <| (← delabAssignableH expr.appArg!) ++ "'"

@[scoped delab app.Assignable.diff]
def delabAssignable.diff : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Assignable.diff 1
  return (mkIdent <| Name.mkSimple ((← delabAssignableH expr.appArg!) ++ "'"))

section Delaborators.Term

def delabSymbol (ctor : Name) (arity : ℕ) (expr : Expr) : DelabM String := do
  guard <| expr.isAppOfArity' ctor arity
  let name := expr.appFn!'.appArg!'
  extractString name

@[scoped delab app.Number.mk]
def delabNumber.num : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Number.mk 3
  let n ← extractNat expr.appFn!'.appFn!'.appArg!'
  let e ← extractNat expr.appFn!'.appArg!'
  let sign ← extractBool expr.appArg!'
  let value := (if sign then (n) * 10 ^ (0 - e) else n * 10 ^ e).toFloat
  let t := Syntax.mkNumLit <| trimTrailingZeros value.toString
  `($t)
  where
    trimTrailingZeros (s : String) : String :=
      if s.contains '.' then
        let s := s.dropRightWhile (·= '0')
        if s.endsWith "." then
           s.dropRight 1
        else
          s
      else
        s

@[scoped delab app.Fn.num]
def delabFn.num : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Fn.num 1
  delab expr.appArg!

@[scoped delab app.Fn.sym]
def delabFn.sym : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Fn.sym 1
  delab expr.appArg!

@[scoped delab app.FunctionSymbol.udef]
def delabFunctionSymbol.mk : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``FunctionSymbol.udef 2
  let name := expr.appFn!.appArg!
  pure <| Lean.mkIdent <| Lean.Name.mkSimple (← extractString name)

partial def delabTermVector (expr : Expr) : DelabM (List (Lean.TSyntax `term)) := do
  guard <| expr.isAppOfArity' ``TermVector.nil 0 || expr.isAppOfArity' ``TermVector.cons 3
  if expr.isAppOfArity' ``TermVector.nil 0 then
    pure []
  else
    let tail := expr.appArg!
    let head := expr.appFn!.appArg!
    pure <| (← delab head) :: (← delabTermVector tail)

-- TODO unbox

@[scoped delab app.Term.var]
def delabTerm.var : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.var 1
  let name := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_term| $name)⟩

@[scoped delab app.Term.neg]
def delabTerm.neg : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.neg 1
  let t ← withAppArg delab
  `(-$t)

@[scoped delab app.Term.plus]
def delabTerm.plus : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.plus 2
  let t₁ ← withNaryArg 0 delab
  let t₂ ← withNaryArg 1 delab
  `($t₁ + $t₂)

@[scoped delab app.Term.times]
def delabTerm.times : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.times 2
  let t₁ ← withNaryArg 0 delab
  let t₂ ← withNaryArg 1 delab
  `($t₁ * $t₂)

-- TODO use dL_term category, adjust delabTermVector
@[scoped delab app.Term.applyFn]
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

@[scoped delab app.Term.differential]
def delabTerm.differential : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Term.differential 1
  let t := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_term| ($t)')⟩

end Delaborators.Term

section Delaborators.Program

@[scoped delab app.Program.const]
def delabConst : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.const 1
  let programSymbol := expr.appArg!
  guard <| programSymbol.isAppOfArity' ``ProgramSymbol.mk 1
  let symbolName := Lean.mkIdent <| Lean.Name.mkSimple (← extractString programSymbol.appArg!)

  return ⟨← `(dL_program| $symbolName:ident)⟩

@[scoped delab app.Program.test]
def delabTest : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.test 1
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| ? $Φ)⟩

@[scoped delab app.Program.assign]
def delabAssign : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.assign 2
  let assignable := ⟨← delab expr.appFn!.appArg!⟩
  let t := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $assignable:ident := $t)⟩

@[scoped delab app.Program.seq]
def delabSequence : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.seq 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $α₁ ; $α₂)⟩

@[scoped delab app.Program.choice]
def delabChoice : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.choice 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $α₁ ∪ $α₂)⟩

@[scoped delab app.Program.loop]
def delabLoop : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Program.loop 1
  let α := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_program| $α*)⟩

@[scoped delab app.ODE.mk]
def delabOde : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``ODE.mk 2
  let var : Q(Assignable):= expr.appFn!.appArg!
  let var' : TSyntax `ident := ⟨← delab q(Assignable.diff $var)⟩
  let term := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_ode| $var':ident = $term)⟩

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

@[scoped delab app.Program.ode]
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

@[scoped delab app.Formula.True]
def delabTrue : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.True 0
  return ⟨← `(dL_formula| true)⟩

@[scoped delab app.Formula.False]
def delabFalse : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.False 0
  return ⟨← `(dL_formula| false)⟩

@[scoped delab app.Formula.and]
def delabAnd : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.and 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ ∧ $Φ₂)⟩

@[scoped delab app.Formula.applyPred]
def delabApplyPred : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.applyPred 2
  let args := (← delabTermVector expr.appArg!).toArray
  let p := Lean.mkIdent <|
    Lean.Name.mkSimple (← delabSymbol ``PredicateSymbol.mk 2 (expr.appFn!.appArg!))
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

@[scoped delab app.Formula.eq]
def delabEq : Delab := delabInEquality ``Formula.eq (fun t₁ t₂ => `($t₁ = $t₂))

@[scoped delab app.Formula.gte]
def delabGte : Delab := delabInEquality ``Formula.gte (fun t₁ t₂ => `($t₁ ≥ $t₂))

@[scoped delab app.Formula.not]
def delabNot : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.not 1
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ¬$Φ)⟩

@[scoped delab app.Formula.or]
def delabOr : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.or 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ ∨ $Φ₂)⟩

@[scoped delab app.Formula.forall]
def delabForall : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.forall 2
  let x := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ∀$x, $Φ)⟩

@[scoped delab app.Formula.exists]
def delabExists : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.exists 2
  let x := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ∃$x, $Φ)⟩

@[scoped delab app.Formula.box]
def delabBox : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.box 2
  let α := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| [$α]$Φ)⟩

@[scoped delab app.Formula.diamond]
def delabDiamond : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.diamond 2
  let α := ⟨← delab expr.appFn!.appArg!⟩
  let Φ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| ⟨$α⟩$Φ)⟩

@[scoped delab app.Formula.implies]
def delabImplies : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.implies 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ → $Φ₂)⟩

@[scoped delab app.Formula.equiv]
def delabEquiv : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.equiv 2
  let Φ₁ := ⟨← delab expr.appFn!.appArg!⟩
  let Φ₂ := ⟨← delab expr.appArg!⟩
  return ⟨←`(dL_formula| $Φ₁ ↔ $Φ₂)⟩

@[scoped delab app.Formula.neq]
def delabNeq : Delab := delabInEquality ``Formula.neq (fun t₁ t₂ => `($t₁ ≠ $t₂))

@[scoped delab app.Formula.gt]
def delabGt : Delab := delabInEquality ``Formula.gt (fun t₁ t₂ => `($t₁ > $t₂))

@[scoped delab app.Formula.lt]
def delabLt : Delab := delabInEquality ``Formula.lt (fun t₁ t₂ => `($t₁ < $t₂))

@[scoped delab app.Formula.lte]
def delabLte : Delab := delabInEquality ``Formula.lte (fun t₁ t₂ => `($t₁ ≤ $t₂))

@[scoped delab app.Formula.ref]
def delabRef : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.ref 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_formula| $α₁:dL_program ≼ $α₂:dL_program)⟩

@[scoped delab app.Formula.progEquiv]
def delabProgEquiv : Delab := do
  let expr ← getExpr
  guard <| expr.isAppOfArity' ``Formula.progEquiv 2
  let α₁ := ⟨← delab expr.appFn!.appArg!⟩
  let α₂ := ⟨← delab expr.appArg!⟩
  return ⟨← `(dL_formula| $α₁:dL_program ≃ $α₂:dL_program)⟩

end Delaborators.Formula

end Delaborators

end Embedding
