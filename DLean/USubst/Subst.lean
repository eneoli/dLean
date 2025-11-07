import DLean.Syntax.Definitions
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics

open Semantics

def Symbol.SubstType : Symbol → Type
  | .Function f => TermVector f.arity → Term
  | .Predicate p => TermVector p.arity → Formula
  | .Program _ => _root_.Program

-- Creating an inductive type for each Symbol kind does not solve
-- the problem of missing Equality Reflection:
/-
  inductive SubstEntry : Type where
    | .fn : (s : Symbol) → (TermVector s.arity → Term) → SubstEntry
    ...
-/

structure SubstEntry : Type where
  symbol : Symbol
  rhs : symbol.SubstType

def Subst.Nodup (σ : List SubstEntry) : Prop :=
  (σ.map SubstEntry.symbol).Nodup

def Subst : Type := { σ : List SubstEntry // Subst.Nodup σ }

theorem Subst.tail_nodup {e : SubstEntry}
                         {σ : List SubstEntry}
                         : Subst.Nodup (e::σ) → Subst.Nodup σ := by
  simp[Subst.Nodup]

def Symbol.default : (symbol : Symbol) → symbol.SubstType
  | .Function f => Term.applyFn (.sym f)
  | .Predicate p => Formula.applyPred p
  | .Program a => Program.const a

def Subst.get (σ : Subst) (symbol : Symbol) : symbol.SubstType :=
  match σ with
    | ⟨.nil, _⟩ => symbol.default
    | ⟨e::σ', h⟩ =>
      if heq : e.symbol = symbol then
        -- I don't like this, but if we stick with returning functions
        -- there is no other way since we encode the arity in the type
        cast (by simp[heq]) e.rhs
      else
        Subst.get ⟨σ', Subst.tail_nodup h⟩ symbol
termination_by
  sizeOf σ.1

section SubstApplication

mutual

def TermVector.applySubst {n : ℕ} (σ : Subst) (ts : TermVector n) : TermVector n :=
  match ts with
    | .nil => .nil
    | .cons t ts => .cons (Term.applySubst σ t) (TermVector.applySubst σ ts)

def Term.applySubst (σ : Subst) (t : Term) :=
  match t with
    | .var _  => t
    | .neg t' => .neg (Term.applySubst σ t')
    | .plus t₁ t₂ => .plus (Term.applySubst σ t₁) (Term.applySubst σ t₂)
    | .times t₁ t₂ => .times (Term.applySubst σ t₁) (Term.applySubst σ t₂)
    | .differential t => .differential (Term.applySubst σ t)
    | .applyFn (.num n) args =>
        let sargs := TermVector.applySubst σ args
        .applyFn (.num n) sargs
    | .applyFn (.sym f) args =>
        let sargs := TermVector.applySubst σ args
        Subst.get σ f sargs

end

mutual

def Formula.applySubst (σ : Subst) (Φ : Formula) := match Φ with
  | .True
  | .False            => Φ
  | .eq t₁ t₂         => .eq (t₁.applySubst σ) (t₂.applySubst σ)
  | .gte t₁ t₂        => .gte (t₁.applySubst σ) (t₂.applySubst σ)
  | .not Φ'           => .not (Φ'.applySubst σ)
  | .and Φ₁ Φ₂        => .and (Φ₁.applySubst σ) (Φ₂.applySubst σ)
  | .forall x Φ       => .forall x (Φ.applySubst σ)
  | .exists x Φ       => .exists x (Φ.applySubst σ)
  | .diamond α Φ      => .diamond (α.applySubst σ) (Φ.applySubst σ)
  | .box α Φ          => .box (α.applySubst σ) (Φ.applySubst σ)
  | .ref α β          => .ref (α.applySubst σ) (β.applySubst σ)
  | .applyPred p args =>
    let sargs := TermVector.applySubst σ args
    Subst.get σ p sargs

def Program.applySubst (σ : Subst) (α : Program) : Program := match α with
  | .assign x t   => .assign x (t.applySubst σ)
  | .test Φ       => .test (Φ.applySubst σ)
  | .ode system Ψ =>
    let ssystem := system.map (fun {var, term} => ODE.mk var (Term.applySubst σ term))
    .ode ssystem (Ψ.applySubst σ)
  | .choice α β   => .choice (α.applySubst σ) (β.applySubst σ)
  | .seq α β      => .seq (α.applySubst σ) (β.applySubst σ)
  | .loop α       => .loop (α.applySubst σ)
  | .const a      => Subst.get σ a

end

end SubstApplication

section SubstAdjoint

open scoped ContDiff

noncomputable def Subst.adjoint (σ : Subst)
                                (i : Interpretation)
                                (v : State)
                                : Interpretation :=
  fun s =>
    match s with
      | .Function f =>
        ⟨
          fun args =>
            let ⟨dots, idots⟩ := i.assignDots args
            let t := σ.get (.Function f) dots
            Term.denote idots v t,
          by
            apply Term.cont_diff
        ⟩
      | .Predicate p =>
        fun args =>
          let ⟨dots, idots⟩ := i.assignDots args
          let Φ := σ.get (.Predicate p) dots
          v ∈ Formula.denote idots Φ
      | .Program a =>
          Program.denote i (σ.get a)

end SubstAdjoint
