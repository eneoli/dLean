import Mathlib.Data.Real.Basic

inductive Variable : Type where
  | variable (name : String) : Variable
  deriving DecidableEq, BEq

inductive Assignable : Type where
  | var  : Variable → Assignable
  | diff : Assignable → Assignable
  deriving DecidableEq, BEq

inductive Function : ℕ → Type where
  | fn (name : String) (arity : ℕ): Function arity
  deriving DecidableEq, BEq

structure Fn where
  name : String
  arity : ℕ
deriving DecidableEq, BEq

mutual
-- Cannot use Vector because of Kernel Bug :(
inductive TermVector : ℕ → Type where
  | nil  : TermVector 0
  | cons : {n: ℕ} → Term → TermVector n → TermVector (n+1)

inductive Term : Type where
  | var          : Assignable  → Term
  | neg          : Term        → Term
  | plus         : Term        → Term       → Term
  | times        : Term        → Term       → Term
  | applyFn      : (f : Fn)    → TermVector f.arity → Term
  | differential : Term        → Term
  deriving DecidableEq
end

def TermVector.toList {n : ℕ} (xs : TermVector n) : List Term := match xs with
  | nil => []
  | cons x xs => x :: TermVector.toList xs

theorem term_vector_list_eq_size {n : ℕ} (ts : TermVector n) : sizeOf ts.toList <= sizeOf ts := by
  apply @TermVector.rec (fun n (ts : TermVector n) => sizeOf ts.toList <= sizeOf ts) (fun t => true)
  <;> simp
  unfold TermVector.toList
  simp
  --
  intros n t s h
  unfold TermVector.toList
  simp[*]
  apply Nat.add_le_add
  apply Nat.add_le_add
  simp[*]
  simp[*]
  exact h

-- mutual
-- instance TermVector.deq {n: ℕ} (a : TermVector n) (b : TermVector n): Decidable (a = b) :=
--   match a, b with
--     | .nil, .nil => isTrue (by rfl)
--     | .cons x xs, .cons y ys => by
--         simp
--         have xyEq := Term.deq x y
--         apply @instDecidableAnd _ _ xyEq (TermVector.deq xs ys)
-- termination_by (sizeOf a + sizeOf b)

-- instance Term.deq (a : Term) (b : Term) : Decidable (Eq a b) := by
--   cases a <;> cases b <;> try exact isFalse Term.noConfusion
--   case
--     -- real.real x y
--   var.var   x y =>
--     simp
--     exact decEq x y
--   case
--     neg.neg x y
--   | differential.differential x y =>
--     simp
--     exact Term.deq x y
--   case
--     plus.plus   x1 y1 x2 y2
--   | times.times x1 y1 x2 y2 =>
--     simp
--     apply @instDecidableAnd _ _ (Term.deq x1 x2) (Term.deq y1 y2)
--   case applyFn.applyFn f1 l1 f2 l2 =>
--     simp
--     if hf : f1 = f2 then
--       have ha : f1.arity = f2.arity := by simp[hf]
--       have htvt : TermVector f2.arity = TermVector f1.arity := by simp[ha]
--       have hd : Decidable (cast htvt l2 = l1) := TermVector.deq (cast htvt l2) l1
--       simp[*]
--       match hd with
--         | isTrue ht => exact isTrue (by
--             apply heq_of_eq_cast
--             simp[ht]
--             exact htvt
--           )
--         | isFalse hf => exact isFalse (by
--           intro x
--           apply hf
--           apply Eq.symm
--           apply eq_cast_iff_heq.mpr
--           exact x
--         )
--     else
--       exact isFalse (by simp[hf])
-- termination_by (sizeOf a + sizeOf b)
-- end

def Term.freeAssignables : (t : Term) → List Assignable
  -- | Term.real _         => []
  | Term.var  v         => [v]
  | Term.neg  n         => Term.freeAssignables n
  | Term.plus  x y
  | Term.times x y      => Term.freeAssignables x ++ Term.freeAssignables y
  | Term.differential t => Term.freeAssignables t
  | Term.applyFn f ts   => List.flatten $ List.map (fun ⟨t, h⟩ => Term.freeAssignables t) (TermVector.toList ts).attach
termination_by t => sizeOf t
decreasing_by
  simp_wf
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  decreasing_trivial
  have ha : sizeOf ts.toList <= sizeOf ts := term_vector_list_eq_size ts
  decreasing_trivial

inductive ProgramConstName : Type where
  | programConstName (name: String) : ProgramConstName
deriving DecidableEq

-- TODO: Is x = 42; an ODE?
-- Differential equations x′ = θ & ψ have to be in explicit form, so y′ and (η)′ cannot occur in θ and x 6 ∈ V ′
structure ODE : Type where
  var: Assignable
  term: Term
deriving DecidableEq

-- set_option diagnostics true

mutual
inductive Program : Type where
  | const   : ProgramConstName  → Program
  | assign  : Assignable → Term → Program
  | test    : Formula    → Program
  | ode     : List ODE   → Formula → Program
  | choice  : Program    → Program → Program
  | seq     : Program    → Program → Program
  | loop    : Program    → Program
deriving DecidableEq
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
  deriving DecidableEq
end

-- declare_syntax_cat dL_program
-- syntax dL_program "*" dL_program : dL_program
-- syntax dL_program ";" dL_program : dL_program
