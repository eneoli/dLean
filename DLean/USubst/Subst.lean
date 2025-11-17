import DLean.Syntax.Definitions
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics
import DLean.Semantics.Coincidence

open Semantics

-- Creating an inductive type for each Symbol kind does not solve
-- the problem of missing Equality Reflection:
-- .. but together with freedom of arity (see commented line in SubstType)
-- this should solve issues of dependent pattern matching
inductive SubstEntry : Type where
  | fn : (f : FunctionSymbol) → (TermVector f.arity → Term) → SubstEntry
  | pred : (p : PredicateSymbol) → (TermVector p.arity → Formula) → SubstEntry
  | prog : (a : ProgramSymbol) → Program → SubstEntry

def SubstEntry.symbol : SubstEntry → Symbol
  | .fn f _ => .Function f
  | .pred p _ => .Predicate p
  | .prog a _ => .Program a

def SubstEntry.freeVars :SubstEntry → Set Assignable
  | .fn f rhs => rhs (Term.dots f.arity) |> Term.freeVars
  | .pred p rhs => rhs (Term.dots p.arity) |> Formula.freeVars
  | .prog _ α => α.freeVars

def Subst.Nodup (σ : List SubstEntry) : Prop :=
  (σ.map SubstEntry.symbol).Nodup

def Subst : Type := { σ : List SubstEntry // Subst.Nodup σ }

def Subst.freeVars (σ : Subst) : Set Assignable :=
  σ.1.foldr ((· ∪ ·) ∘ SubstEntry.freeVars) ∅

theorem Subst.tail_nodup {e : SubstEntry}
                         {σ : List SubstEntry}
                         : Subst.Nodup (e::σ) → Subst.Nodup σ := by
  simp[Subst.Nodup]

def Symbol.SubstType : Symbol → Type
  | .Function f => TermVector f.arity → Term
  | .Predicate p => TermVector p.arity → Formula
  | .Program _ => _root_.Program

def SubstEntry.rhs (e : SubstEntry) : e.symbol.SubstType :=
  match e with
    | .fn _ rhs => rhs
    | .pred _ rhs => rhs
    | .prog _ rhs => rhs

def Symbol.default : (symbol : Symbol) → symbol.SubstType
  | .Function f => Term.applyFn (.sym f)
  | .Predicate p => Formula.applyPred p
  | .Program a => Program.const a

def Subst.get (σ : Subst) (symbol : Symbol) : symbol.SubstType :=
  match σ with
    | ⟨.nil, _⟩ => symbol.default
    | ⟨e::σ', h⟩ =>
      if heq : symbol = e.symbol then
        heq ▸ e.rhs
      else
        Subst.get ⟨σ', Subst.tail_nodup h⟩ symbol
termination_by
  σ.1

section SubstApplication

-- TODO Subst admissible?
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
        let dots := Term.dots f.arity
        let t := σ.get (.Function f) dots
        ⟨
          fun args ↦
            let idots := i.assignDots args
            Term.denote idots v t,
          by
            have hg := @Term.contDiff f.arity i v ∅ t
            have hf : ContDiff ℝ ∞ (fun x ↦ (⟨x, fun _ ↦ 0⟩ :
              (Fin f.arity → ℝ) × ({a // a ∈ (∅ : Finset Assignable)} → ℝ))) :=
                contDiff_prodMk_left (fun _ ↦ 0)

            exact ContDiff.comp hg hf
        ⟩
      | .Predicate p =>
        let dots := Term.dots p.arity
        let Φ := σ.get (.Predicate p) dots
        fun args ↦
          let idots := i.assignDots args
          v ∈ Formula.denote idots Φ
      | .Program a =>
          Program.denote i (σ.get a)

end SubstAdjoint

section Theorems

theorem Subst.free_vars_head {σ : Subst}
                             {e : SubstEntry}
                             {h : Subst.Nodup (e :: σ.1)}
                             : e.freeVars ⊆ Subst.freeVars (⟨e :: σ.1, h⟩) := by
  simp[Subst.freeVars]

theorem Subst.free_vars_tail {σ : Subst}
                             {e : SubstEntry}
                             {h : Subst.Nodup (e :: σ.1)}
                             : σ.freeVars ⊆ Subst.freeVars (⟨e :: σ.1, h⟩) := by
  simp[Subst.freeVars]

def Subst.free_vars_subset_fun {σ : Subst}
                               {f : FunctionSymbol}
                               : ↑(σ.get f (Term.dots f.arity)).freeVars ⊆ σ.freeVars := by
  match h : σ with
    | ⟨.nil, _⟩ =>
      simp[Subst.get, Subst.freeVars, Symbol.default, Term.freeVars, Term.dots_free_vars]
    | ⟨.cons x xs, hnodup⟩ =>
      let σ' : Subst := ⟨xs, Subst.tail_nodup hnodup⟩
      simp[Subst.get]
      by_cases h : x.symbol = Symbol.Function f
      .
        simp[h]
        have := @Subst.free_vars_head σ' x hnodup
        simp[σ', SubstEntry.freeVars] at this
        match hx : x with
          | .fn f' rhs =>
            have hf : f' = f := by
              simp[SubstEntry.symbol] at h
              assumption
            cases hf
            simp at this
            simp[SubstEntry.rhs]
            exact this
          | .pred p _ => simp[SubstEntry.symbol] at h
          | .prog a _ => simp[SubstEntry.symbol] at h
      .
        have := @Subst.free_vars_tail σ' x hnodup
        have := @Subst.free_vars_subset_fun σ' f
        grind only [= Set.subset_def, = Finset.mem_coe]
termination_by
  σ.1

def Subst.free_vars_subset_pred {σ : Subst}
                                {p : PredicateSymbol}
                                : ↑(σ.get p (Term.dots p.arity)).freeVars ⊆ σ.freeVars := by
  sorry

def Subst.admissible_adjoint {v w : State}
                             {σ : Subst}
                             {i : Interpretation}
                             (heq : State.isEqOn v w σ.freeVars)
                             : Subst.adjoint σ i v = Subst.adjoint σ i w := by
  funext x
  match x with
    | .Function f =>
      simp[Subst.adjoint]
      congr
      funext args
      apply Term.coincidence
      and_intros
      .
        apply State.is_eq_on_subset
        . exact heq
        . apply Subst.free_vars_subset_fun
      . simp
    | .Predicate p =>
      simp[Subst.adjoint]
      funext args
      apply propext
      apply Iff.intro
      all_goals
      apply Formula.coincidence
      and_intros
      . apply State.is_eq_on_subset
        . first | exact heq | exact State.eq_on_symm heq
        . apply Subst.free_vars_subset_pred
      . simp
    | .Program a => simp[Subst.adjoint]

end Theorems
