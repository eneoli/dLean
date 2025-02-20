import Mathlib.Data.Real.Basic

inductive Variable : Type where
  | variable (name : String) : Variable
  deriving DecidableEq, BEq

inductive Assignable : Type where
  | var  : Variable -> Assignable
  | diff : Assignable -> Assignable
  deriving DecidableEq, BEq

inductive Function : ℕ → Type where
  | fn (name : String) (arity : ℕ): Function arity
  deriving DecidableEq, BEq

mutual
-- Cannot use Vector because of Kernel Bug :(
inductive TermVector : ℕ → Type where
  | nil  : TermVector 0
  | cons : {n: ℕ} → Term → TermVector n -> TermVector (n+1)

inductive Term : Type where
  | real         : ℝ           → Term
  | var          : Assignable  → Term
  | neg          : Term        → Term
  | plus         : Term        → Term       → Term
  | times        : Term        → Term       → Term
  | applyFn      : {n : ℕ}     → Function n → TermVector n → Term
  | differential : Term        → Term
end

noncomputable instance Term.deq: DecidableEq Term := fun a b => by
  cases a <;> cases b <;> try exact isFalse Term.noConfusion
  case
    real.real x y
  | var.var   x y =>
    simp
    exact decEq x y
  case
    neg.neg x y
  | differential.differential x y =>
    simp
    exact deq x y
  case
    plus.plus   x1 y1 x2 y2
  | times.times x1 y1 x2 y2 =>
    simp
    apply @instDecidableAnd _ _ (deq x1 x2) (deq y1 y2)
  case applyFn.applyFn n1 f1 l1 n2 f2 l2 =>
    simp
    if hn : n1 = n2 then
      have f2' : Function n1 := by simp[hn] ; exact f2
      if hf : f1 = f2' then
        -- simp[*]
        -- apply eq_cast_iff_heq.mpr
        -- apply @instDecidableAnd _ _ (sorry) (sorry)
        sorry
      else
        exact isFalse (by simp[hf])
    else
      exact isFalse (by simp[hn])

noncomputable instance TermVector.deq {n: ℕ}: DecidableEq (TermVector n) := fun a b => by
  cases a <;> cases b <;> try exact isFalse TermVector.noConfusion
  case nil.nil => exact isTrue (by rfl)
  case cons.cons n x xs y ys =>
    simp
    apply @instDecidableAnd _ _ (Term.deq x y) (TermVector.deq xs ys)

instance mem (n : ℕ) : Membership Term (TermVector n) where
  mem := fun A => fun a =>  match A with
  | TermVector.nil => false
  | TermVector.cons x xs => if x == a then true else mem xs a

def TermVector.toList {n : ℕ} (xs : TermVector n) : List Term := match xs with
  | nil => []
  | cons x xs => x :: TermVector.toList xs

def Term.freeAssignables : (t : Term) → List Assignable
  | Term.real _         => []
  | Term.var  v         => [v]
  | Term.neg  n         => Term.freeAssignables n
  | Term.plus  x y
  | Term.times x y      => Term.freeAssignables x ++ Term.freeAssignables y
  | Term.differential t => Term.freeAssignables t
  | Term.applyFn f ts   => List.flatten $ List.map (fun ⟨t, h⟩ => Term.freeAssignables t) (TermVector.toList ts).attach
termination_by t => t
decreasing_by
  simp_wf
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial

inductive ProgramConstName : Type where
  | programConstName (name: String) : ProgramConstName

-- TODO: Is x = 42; an ODE?
-- Differential equations x′ = θ & ψ have to be in explicit form, so y′ and (η)′ cannot occur in θ and x 6 ∈ V ′
structure ODE : Type where
  var: Assignable
  term: Term

mutual
inductive Program : Type where
  | const   : ProgramConstName  → Program
  | assign  : Assignable → Term → Program
  | test    : Formula    → Program
  | ode     : List ODE   → Formula → Program
  | choice  : Program    → Program → Program
  | seq     : Program    → Program → Program
  | loop    : Program    → Program
inductive Formula : Type where
  | True     : Formula
  | False    : Formula
  | equal    : Term      → Term    → Formula
  | notEqual : Term      → Term    → Formula
  | gte      : Term      → Term    → Formula
  | gt       : Term      → Term    → Formula
  | lt       : Term      → Term    → Formula
  | lte      : Term      → Term    → Formula
  | not      : Formula   → Formula → Formula
  | and      : Formula   → Formula → Formula
  | or       : Formula   → Formula → Formula
  | imply    : Formula   → Formula → Formula
  | equiv    : Formula   → Formula → Formula
  | forall   : Variable  → Formula → Formula
  | exists   : Variable  → Formula → Formula
  | diamond  : Program   → Formula → Formula
  | box      : Program   → Formula → Formula
end

-- declare_syntax_cat dL_program
-- syntax dL_program "*" dL_program : dL_program
-- syntax dL_program ";" dL_program : dL_program
