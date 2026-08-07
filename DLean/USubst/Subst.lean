import DLean.Syntax.Definitions
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics
import DLean.Semantics.Coincidence
import DLean.Util.FCSet

open Semantics

inductive SubstEntry : Type where
  | fn : (f : FunctionSymbol) → Term → SubstEntry
  | pred : (p : PredicateSymbol) → Formula → SubstEntry
  | prog : (a : ProgramSymbol) → Program → SubstEntry

def SubstEntry.symbol : SubstEntry → Symbol
  | .fn f _ => .Function f
  | .pred p _ => .Predicate p
  | .prog a _ => .Program a

/-- Decidable version. -/
def SubstEntry.freeVars : SubstEntry → FCSet Assignable
  | .fn _ rhs => rhs |> Term.freeVars |> .Finite
  | .pred _ rhs => rhs |> Formula.freeVars'
  | .prog _ _ => ∅

def Subst.Nodup (σ : List SubstEntry) : Prop :=
  (σ.map SubstEntry.symbol).Nodup

def Subst : Type := { σ : List SubstEntry // Subst.Nodup σ }

theorem Subst.tail_nodup {e : SubstEntry}
                         {σ : List SubstEntry}
                         : Subst.Nodup (e::σ) → Subst.Nodup σ := by
  simp[Subst.Nodup]

/-- Decidable version.
 -- Restricts σ on the symbols contained in S if some. -/
def Subst.freeVars (σ : Subst) (S : Option (Finset Symbol)) : FCSet Assignable :=
  match σ with
    | ⟨.nil, _⟩ => ∅
    | ⟨e::xs, h⟩ =>
      let σ' : Subst := ⟨xs, Subst.tail_nodup h⟩
      match S with
        | .none => e.freeVars ∪ σ'.freeVars S
        | .some S =>
          if e.symbol ∈ S then
            e.freeVars ∪ σ'.freeVars S
          else
            σ'.freeVars S
termination_by
  σ.1

def Symbol.SubstType : Symbol → Type
  | .Function _ => Term
  | .Predicate _ => Formula
  | .Program _ => _root_.Program

def SubstEntry.rhs (e : SubstEntry) : e.symbol.SubstType :=
  match e with
    | .fn _ rhs => rhs
    | .pred _ rhs => rhs
    | .prog _ rhs => rhs

def Symbol.default : (symbol : Symbol) → symbol.SubstType
  | .Function f => Term.applyFn (.sym f) (Term.dots f.arity)
  | .Predicate p => Formula.applyPred p (Term.dots p.arity)
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

def Subst.size (σ : Subst) := match σ with
  | ⟨[],_⟩ => (0,0)
  | ⟨e::σ', h⟩ => let ⟨ar, len⟩ := Subst.size ⟨σ', Subst.tail_nodup h⟩
                  (max e.symbol.arity ar, len + 1)
termination_by σ.1

section SubstApplication

/-- Restricts σ on the symbols in S. -/
abbrev Subst.admissible (σ : Subst) (U : FCSet Assignable) (S : Finset Symbol) : Prop :=
  (σ.freeVars S) ∩ U = ∅

def TermVector.toSubstAux {n : ℕ} (ts : TermVector n) (k : ℕ) : List SubstEntry :=
  match ts with
  | .nil => []
  | .cons t ts => (.fn (.dot k) t)::(TermVector.toSubstAux ts (k + 1))

lemma TermVector.toSubstLemma
  {n : ℕ} (ts : TermVector n) (k : ℕ) :
  Subst.Nodup (ts.toSubstAux k)
  ∧ ∀ x ∈ ts.toSubstAux k,
      ∃ m, k ≤ m ∧ m < k + n ∧ x.symbol = Symbol.Function (FunctionSymbol.dot m) := by
match ts with
| .nil =>
    exact ⟨by simp [TermVector.toSubstAux, Subst.Nodup],
           by simp [TermVector.toSubstAux]⟩
| @TermVector.cons n t ts =>
    have ⟨hdup, h⟩ := TermVector.toSubstLemma ts (k + 1)
    simp [TermVector.toSubstAux]
    constructor
    · simp [Subst.Nodup]
      refine ⟨?_, hdup⟩
      intros x hx
      specialize h x hx
      obtain ⟨m, hm₁, hm₂, hs⟩ := h
      rw [hs]
      simp [SubstEntry.symbol]
      grind

    and_intros
    .
      apply Exists.intro k
      and_intros
      . omega
      . omega
      . simp_all[SubstEntry.symbol]
    · intro x hx
      · specialize h x hx
        obtain ⟨m, hm₁, hm₂, hs⟩ := h
        exact ⟨m, by grind, by grind, hs⟩



-- Assigns the n elements of a TermVector to the first n dots.
def TermVector.toSubst {n : ℕ} (ts : TermVector n) : Subst :=
  ⟨ts.toSubstAux 0, (ts.toSubstLemma 0).1⟩

lemma TermVector.toSubstAux_size {n : ℕ}
                                 (ts : TermVector n)
                                 (k : ℕ)
                                 (hs : Subst.Nodup (ts.toSubstAux k))
  : Subst.size ⟨ts.toSubstAux k, hs⟩ = (0, n) := by
    cases ts with
      | nil => simp only [toSubstAux, Subst.size]
      | cons t ts =>
        have := TermVector.toSubstAux_size ts
        simp_all [toSubstAux, Subst.size, SubstEntry.symbol,
          Symbol.arity, FunctionSymbol.arity]

lemma TermVector.toSubst_size {n : ℕ} (ts : TermVector n) : ts.toSubst.size = (0,n) := by
  simp[TermVector.toSubst]
  apply TermVector.toSubstAux_size

def Subst.mem (σ : Subst) (s : Symbol) : Prop := match σ with
    | ⟨[], _⟩ => False
    | ⟨e::es, h⟩ => s = e.symbol ∨ Subst.mem (⟨es, Subst.tail_nodup h⟩ : Subst) s
termination_by
  σ.1

instance : Membership Symbol Subst where
  mem := Subst.mem


instance Subst.mem_dec (s : Symbol) (σ : Subst) : Decidable (s ∈ σ) := by
  match σ with
    | ⟨.nil, _⟩ =>
      simp_all[Membership.mem]
      constructor
      simp_all[Subst.mem]
    | ⟨.cons head tail, h⟩ =>
      simp_all[Membership.mem, Subst.mem]
      by_cases s = head.symbol
      .
        apply Decidable.isTrue
        simp_all
      .
        let := Subst.mem_dec s ⟨tail, Subst.tail_nodup h⟩
        simp_all
        assumption
termination_by
  sizeOf σ.1

instance Subst.membership_decidable (σ : Subst) (f : FunctionSymbol) :
  Decidable ((.Function f) ∈ List.map SubstEntry.symbol σ.1) := by
  induction σ.1
  . simp_all ; constructor ; trivial
  .
    next head tail ih =>
    rw[List.map_cons]
    by_cases f = head.symbol
    .
      apply Decidable.isTrue
      simp_all
    .
      rw[List.mem_map] at ih
      simp_all
      assumption

lemma Subst.symbol_size (σ : Subst) (s : Symbol) :
  (s ∈ σ) → σ.size.1 ≥ s.arity ∧ σ.size.2 ≥ 1 := by
  intro h
  match σ with
    | ⟨[], _⟩ => simp_all[Subst.mem, Membership.mem]
    | ⟨e::es, hs⟩ =>
      simp_all[Subst.size, Subst.mem, Membership.mem]
      cases h
      . grind
      .
        have := Subst.symbol_size ⟨es, Subst.tail_nodup hs⟩ s (by simp_all[Membership.mem])
        grind
termination_by
  sizeOf σ.1

mutual

def TermVector.applySubst {n : ℕ} (σ : Subst) (U : FCSet Assignable) (ts : TermVector n) : Option (TermVector n) :=
  match ts with
    | .nil => pure .nil
    | .cons t ts => do
      return .cons (← Term.applySubst σ U t) (← TermVector.applySubst σ U ts)
termination_by (σ.size, sizeOf ts)
decreasing_by
all_goals simp_wf
all_goals grind only [= Prod.lex_def]


def Term.applySubst (σ : Subst) (U : FCSet Assignable) (t : Term) : Option Term :=
  match t with
    | .var x  => return .var x
    | .neg t' => do return .neg (← Term.applySubst σ U t')
    | .plus t₁ t₂ => do return .plus (← Term.applySubst σ U t₁) (← Term.applySubst σ U t₂)
    | .times t₁ t₂ => do return .times (← Term.applySubst σ U t₁) (← Term.applySubst σ U t₂)
    | .differential t => do
        return .differential (← Term.applySubst σ .univ t)
    | .applyFn (.num _) _ => do
        -- let sargs ← TermVector.applySubst σ U args
        return t
    | .applyFn (.sym f) args => do
        let sargs ← TermVector.applySubst σ U args
        if (.Function f) ∈ σ then
          guard <| .Finite (Subst.get σ f).freeVars ∩ U = ∅
          Term.applySubst (sargs.toSubst) ∅ (Subst.get σ f)
        else
          return .applyFn (.sym f) sargs

termination_by (σ.size, sizeOf t)
decreasing_by
all_goals simp_wf
all_goals (try grind only [= Prod.lex_def])
next hin =>
  rw[TermVector.toSubst_size sargs]
  apply Subst.symbol_size at hin
  grind only [= Prod.lex_def]

end

/- Precomputes the bound variables post-substitution.
   Used for substitution of loops. -/
def Program.substBoundVars (σ : Subst) (α : Program) : FCSet Assignable :=
  match α with
  | .const a => (σ.get a).boundVars'
  | .test _ => ∅
  | .assign x _
  | .random x => {x}
  | .choice α β
  | .seq α β => α.substBoundVars σ ∪ β.substBoundVars σ
  | .loop α => α.substBoundVars σ
  | .ode _ _ => α.boundVars'


mutual

def Formula.applySubst (σ : Subst) (U : FCSet Assignable) (Φ : Formula) : Option Formula := match Φ with
  | .True
  | .False            => Φ
  | .eq t₁ t₂         => do return .eq (← t₁.applySubst σ U) (← t₂.applySubst σ U)
  | .gte t₁ t₂        => do return .gte (← t₁.applySubst σ U) (← t₂.applySubst σ U)
  | .not Φ'           => do return .not (← Φ'.applySubst σ U)
  | .and Φ₁ Φ₂        => do return .and (← Φ₁.applySubst σ U) (← Φ₂.applySubst σ U)
  | .forall x Φ       => do
      return .forall x (← Φ.applySubst σ ({.var x} ∪ U))
  | .exists x Φ       => do
      return .exists x (← Φ.applySubst σ ({.var x} ∪ U))
  | .diamond α Φ      => do
      let ⟨V,σα⟩ ← α.applySubst σ U
      return .diamond σα (← Φ.applySubst σ V)
  | .box α Φ          => do
      let ⟨V,σα⟩ ← α.applySubst σ U
      return .box σα (← Φ.applySubst σ V)
  | .ref α β          => do
      return .ref (← α.applySubst σ U).2 (← β.applySubst σ U).2
  | .applyPred p args => do
      let sargs ← TermVector.applySubst σ U args
      if (.Predicate p) ∈ σ then
        guard <| (Subst.get σ p).freeVars' ∩ U = ∅
        Formula.applySubst (sargs.toSubst) ∅ (Subst.get σ p)
      else
        return .applyPred p sargs
termination_by (σ.size, Φ.size)
decreasing_by
all_goals (try simp_all[Formula.size] ; grind)
next hin =>
  rw[TermVector.toSubst_size sargs]
  apply Subst.symbol_size at hin
  grind only [= Prod.lex_def]

def Program.applySubst (σ : Subst) (U : FCSet Assignable) (α : Program) : Option (FCSet Assignable × Program) := match α with
  | .assign x t   => return ⟨{x} ∪ U, .assign x (← t.applySubst σ U)⟩
  | .random x     => return ⟨{x} ∪ U, .random x⟩
  | .test Φ       => return ⟨U, .test (← Φ.applySubst σ U)⟩
  | .ode system Ψ => do
    let vars := system.assignables
    let vars' := vars.map Assignable.diff_emb
    let V := (.Finite (vars ∪ vars')) ∪ U
    let σΨ ← Ψ.applySubst σ V

    let ssystem ← system.mapM (fun {var, term} => do return ODE.mk var (← Term.applySubst σ V term))
    return ⟨V, .ode ssystem σΨ⟩
  | .choice α β   => do
    let ⟨V, σα⟩ ← α.applySubst σ U
    let ⟨W, σβ⟩ ← β.applySubst σ U
    return ⟨V ∪ W, .choice σα σβ⟩
  | .seq α β      => do
    let ⟨V, σα⟩ ← α.applySubst σ U
    let ⟨W, σβ⟩ ← β.applySubst σ V
    return ⟨W, .seq σα σβ⟩
  | .loop α       => do
    let V := α.substBoundVars σ ∪ U
    let ⟨W,σα⟩ ← α.applySubst σ V
    return ⟨W, .loop σα⟩
  | .const a      =>
    let σα := Subst.get σ a
    return ⟨σα.boundVars' ∪ U, σα⟩
termination_by (σ.size, α.size)
decreasing_by
all_goals (simp_all[Program.size] ; grind)

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
        let t := σ.get (.Function f)
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
        let Φ := σ.get (.Predicate p)
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
                             : (e.freeVars : Set Assignable)
                             ⊆ Subst.freeVars (⟨e :: σ.1, h⟩) .none := by
  simp[Subst.freeVars]

theorem Subst.free_vars_tail {σ : Subst}
                             {e : SubstEntry}
                             {h : Subst.Nodup (e :: σ.1)}
                             {S : Option (Finset Symbol)}
                             : (σ.freeVars S : Set Assignable)
                             ⊆ Subst.freeVars ⟨e :: σ.1, h⟩ S := by
  match S with
    | .none => simp[Subst.freeVars]
    | .some S =>
      by_cases h : ((SubstEntry.symbol e) ∈ S)
      all_goals simp[Subst.freeVars, h]

-- Unused
lemma Subst.get_fn_head {σ : Subst}
                        {f : FunctionSymbol}
                        {rhs : Term}
                        {h : Subst.Nodup (.fn f rhs :: σ.1)}
                        : Subst.get ⟨.fn f rhs :: σ.1, h⟩ (Symbol.Function f) = rhs := by
  simp[Subst.get, SubstEntry.symbol, SubstEntry.rhs]

lemma Subst.get_pred_head {σ : Subst}
                          {p : PredicateSymbol}
                          {rhs : Formula}
                          {h : Subst.Nodup (.pred p rhs :: σ.1)}
                          : Subst.get ⟨.pred p rhs :: σ.1, h⟩ (Symbol.Predicate p) = rhs := by
  simp[Subst.get, SubstEntry.symbol, SubstEntry.rhs]

lemma Subst.get_tail {σ : Subst}
                     {s : Symbol}
                     {e : SubstEntry}
                     {h₁ : Subst.Nodup (e :: σ.1)}
                     {h₂ : ¬s = e.symbol}
                     : Subst.get ⟨e :: σ.1, h₁⟩ s = σ.get s := by
  simp_all[Subst.get]

theorem Subst.freeVars_symbol_subset (σ : Subst)
                                       {S₁ : Finset Symbol}
                                       {S₂ : Finset Symbol}
                                       (hs : S₁ ⊆ S₂)
  : (Subst.freeVars σ S₁).toSet ⊆ (Subst.freeVars σ S₂).toSet := by
  intro h
  match σ with
    | ⟨.nil, _⟩ =>
      simp[Subst.freeVars]
    | ⟨e::σ', hsubst⟩ =>
      have : (Subst.freeVars ⟨σ', Subst.tail_nodup hsubst⟩ S₁).toSet ⊆
        (Subst.freeVars ⟨σ', Subst.tail_nodup hsubst⟩ S₂).toSet := by
        apply Subst.freeVars_symbol_subset _ hs
      unfold Subst.freeVars
      simp only
      split
      .
        have : e.symbol ∈ S₂ := by grind only [= Finset.subset_iff]
        simp_all only [FCSet.to_set_union, Set.mem_union, ↓reduceIte]
        grind only [= Finset.subset_iff, = Set.subset_def]
      .
        intro
        split
        . grind only [= Set.mem_union, = Set.subset_def, FCSet.to_set_union]
        . grind only [= Set.subset_def]

termination_by
  σ.1

theorem Subst.freeVars_symbol_subset_none {σ : Subst}
                                          {S : Finset Symbol}
  : (Subst.freeVars σ S).toSet ⊆ (Subst.freeVars σ none).toSet := by
  match σ with
    | ⟨.nil, _⟩ =>
      simp[Subst.freeVars]
    | ⟨e::σ', hsubst⟩ =>
      have := @Subst.freeVars_symbol_subset_none ⟨σ', Subst.tail_nodup hsubst⟩ S
      unfold Subst.freeVars
      simp only [FCSet.to_set_union]
      split
      . simp only [FCSet.to_set_union]
        exact Set.union_subset_union_right _ this
      . exact Set.subset_union_of_subset_right this _
termination_by
  σ.1

theorem Subst.freeVars_symbol_union (σ : Subst)
                                    {S₁ : Finset Symbol}
                                    {S₂ : Finset Symbol}
  : (Subst.freeVars σ S₁).toSet ∪ (Subst.freeVars σ S₂).toSet =
    (Subst.freeVars σ (some (S₁ ∪ S₂))).toSet := by
  apply Set.Subset.antisymm
  .
    have h₁ : (σ.freeVars S₁).toSet ⊆ (σ.freeVars (some (S₁ ∪ S₂))).toSet :=
      Subst.freeVars_symbol_subset _ Finset.subset_union_left
    have h₂ : (σ.freeVars S₂).toSet ⊆ (σ.freeVars (some (S₁ ∪ S₂))).toSet :=
      Subst.freeVars_symbol_subset _ Finset.subset_union_right
    exact Set.union_subset h₁ h₂
  .
    intro h
    match σ with
      | ⟨.nil, _⟩ => simp only [freeVars, FCSet.to_set_empty, Set.mem_empty_iff_false,
        Set.union_self, imp_self]
      | ⟨e :: σ', hsubst⟩ =>
        simp only [freeVars, Finset.mem_union, Set.mem_union]
        have := @Subst.freeVars_symbol_union ⟨σ', Subst.tail_nodup hsubst⟩ S₁ S₂
        grind only [= Set.mem_union, FCSet.to_set_union]
termination_by
  σ.1

theorem Subst.free_vars_subset_fun {σ : Subst}
                                   {f : FunctionSymbol}
                                   : ((σ.get f).freeVars : Set Assignable)
                                   ⊆ σ.freeVars (some (Function.signature (Fn.sym f))) := by
  match h : σ with
    | ⟨.nil, _⟩ => simp[Subst.get, Symbol.default, Term.freeVars]
    | ⟨.cons x xs, hnodup⟩ =>
      let σ' : Subst := ⟨xs, Subst.tail_nodup hnodup⟩
      simp[Subst.get]
      by_cases h : x.symbol = Symbol.Function f
      .
        have := @Subst.free_vars_head σ' x hnodup
        match hx : x with
          | .pred _ _ => simp[SubstEntry.symbol] at h
          | .prog _ _ => simp[SubstEntry.symbol] at h
          | .fn f' rhs =>
            simp_all[SubstEntry.symbol]
            cases h
            simp_all[σ', Subst.freeVars, SubstEntry.freeVars, SubstEntry.rhs, Function.signature]
      .
        have := @Subst.free_vars_tail σ' x hnodup
        have := @Subst.free_vars_subset_fun σ' f
        grind only [= Set.subset_def, = Finset.mem_coe]
termination_by
  σ.1

theorem Subst.free_vars_subset_pred {σ : Subst}
                                    {p : PredicateSymbol}
                                    : ((σ.get p).freeVars : Set Assignable)
                                    ⊆ σ.freeVars (some {.Predicate p}) := by
  match σ with
    | ⟨.nil, _⟩ => simp[Subst.get, Symbol.default, Formula.freeVars]
    | ⟨.cons x xs, hnodup⟩ =>
      let σ' : Subst := ⟨xs, Subst.tail_nodup hnodup⟩
      simp[Subst.get]
      by_cases h : x.symbol = Symbol.Predicate p
      .
        have := @Subst.free_vars_head σ' x hnodup
        match hx : x with
          | .fn _ _ => simp[SubstEntry.symbol] at h
          | .prog _ _ => simp[SubstEntry.symbol] at h
          | .pred p' rhs =>
            simp_all[SubstEntry.symbol]
            cases h
            simp_all[σ', Subst.freeVars, SubstEntry.freeVars, SubstEntry.rhs]
            rw[Formula.free_vars_decidable (rhs)]
            simp
      .
        have := @Subst.free_vars_tail σ' x hnodup
        have := @Subst.free_vars_subset_pred σ' p
        grind only [= Set.subset_def]
termination_by
  σ.1

theorem Subst.admissible_subst_cons {σ : Subst}
                                    {e : SubstEntry}
                                    {U : FCSet Assignable}
                                    {S : Finset Symbol}
                                    (hsubst : Subst.Nodup (e :: σ.1))
  : Subst.admissible ⟨e :: σ.1, hsubst⟩ U S
  ↔ (e.symbol ∈ S → e.freeVars ∩ U = ∅) ∧ Subst.admissible σ U S := by
  simp_all[Subst.admissible, Subst.freeVars]
  grind

theorem Subst.admissible_symbol_subset {σ : Subst}
                                       {U : FCSet Assignable}
                                       {S₁ : Finset Symbol}
                                       {S₂ : Finset Symbol}
                                       (hs : S₂ ⊆ S₁)
  : Subst.admissible σ U S₁ → Subst.admissible σ U S₂ := by
  have := Subst.freeVars_symbol_subset σ hs
  simp only [FCSet.to_set_eq, FCSet.to_set_inter, FCSet.to_set_empty]
  grind only [= Set.mem_empty_iff_false, = Set.subset_def, = Set.mem_inter_iff]

theorem Subst.admissible_symbol_union {σ : Subst}
                                      {U : FCSet Assignable}
                                      {A : Finset Symbol}
                                      {B : Finset Symbol}
  : σ.admissible U (A ∪ B) ↔ σ.admissible U A ∧ σ.admissible U B := by
  have := @Subst.freeVars_symbol_union σ A B
  simp only [FCSet.to_set_eq, FCSet.to_set_inter, FCSet.to_set_empty]
  grind only [= Set.mem_union, = Set.mem_empty_iff_false, = Set.mem_inter_iff, cases Or]

theorem Subst.admissible_get_fn_subset {σ : Subst}
                                       {U : FCSet Assignable}
                                       {S : Finset Symbol}
                                       (f : FunctionSymbol)
                                       (hf : .Function f ∈ S)
                                       (hA : Subst.admissible σ U S)
  : ((Subst.get σ f).freeVars : Set _) ⊆ (U : Set Assignable)ᶜ := by
  simp[Subst.admissible] at hA
  calc ↑(Term.freeVars (σ.get (Symbol.Function f)))
    _ ⊆ (σ.freeVars (some (Function.signature (.sym f)))).toSet :=
      Subst.free_vars_subset_fun
    _ ⊆ (σ.freeVars (some S)).toSet :=
      Subst.freeVars_symbol_subset _ (Finset.singleton_subset_iff.mpr hf)
    _ ⊆ U.toSetᶜ :=
      Disjoint.subset_compl_right (Set.disjoint_iff_inter_eq_empty.mpr hA)

theorem Subst.admissible_get_pred_subset {σ : Subst}
                                         {U : FCSet Assignable}
                                         {S : Finset Symbol}
                                         (p : PredicateSymbol)
                                         (hp : .Predicate p ∈ S)
                                         (hA : Subst.admissible σ U S)
  : ((Subst.get σ p).freeVars : Set _) ⊆ (U : Set Assignable)ᶜ := by
  simp[Subst.admissible] at hA
  calc ↑(σ.get (.Predicate p)).freeVars
    _ ⊆ (σ.freeVars (some {.Predicate p})).toSet :=
      Subst.free_vars_subset_pred
    _ ⊆ (σ.freeVars (some S)).toSet :=
      Subst.freeVars_symbol_subset _ (Finset.singleton_subset_iff.mpr hp)
    _ ⊆ U.toSetᶜ :=
      Disjoint.subset_compl_right (Set.disjoint_iff_inter_eq_empty.mpr hA)

-- theorem Subst.adjoint_nil (i : Interpretation)
--                           (v : State)
--                           {hsubst : Subst.Nodup []}
--   : Subst.adjoint ⟨[], hsubst⟩ i v = i := by
--   funext s
--   simp[Subst.adjoint]
--   match s with
--     | .Function f =>
--       simp[Subst.get, Symbol.default, Term.denote]
--       congr
--       -- funext
--       match hf : f with
--         | .dot n =>
--           simp_all[FunctionSymbol.arity]
--           funext args
--           have : args = fun x ↦ Term.denote i v TermVector.nil.toVector[x] :=  by grind
--           aesop
--         | .udef name arity =>
--           funext args
--           simp_all[Interpretation.assignDots]
--           have : args = fun x ↦
--                           Term.denote (i.assignDots args)
--   v
--  (Term.dots (FunctionSymbol.udef name arity).arity).toVector[↑x] := by
--             funext n
--             simp_all
--             sorry

--           sorry
--     | .Predicate p => sorry
--     | .Program a => simp[Subst.get, Symbol.default, Program.denote]

theorem Subst.admissible_adjoint {v w : State}
                                 {σ : Subst}
                                 {i : Interpretation}
                                 (heq : State.isEqOn v w (σ.freeVars .none))
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
        apply Set.EqOn.mono
        . trans
          . exact Subst.free_vars_subset_fun
          . exact Subst.freeVars_symbol_subset_none
        . assumption
      . simp
    | .Predicate p =>
      simp[Subst.adjoint]
      funext args
      apply propext
      apply Iff.intro
      all_goals
      apply Formula.coincidence
      and_intros
      . apply Set.EqOn.mono
        . trans
          . exact Subst.free_vars_subset_pred
          . exact Subst.freeVars_symbol_subset_none
        . first | exact heq | exact Set.EqOn.symm heq
      . simp
    | .Program a => simp[Subst.adjoint]

theorem Subst.admissible_adjoint.term {v w μ : State}
                                      {σ : Subst}
                                      {i : Interpretation}
                                      {t : Term}
                                      {U : FCSet Assignable}
                                      (hA : Subst.admissible σ U t.signature)
                                      (hS : State.isEqOn v w Uᶜ)
                                      : Term.denote (Subst.adjoint σ i v) μ t
                                      = Term.denote (Subst.adjoint σ i w) μ t := by
  match t with
    | .var _ => simp[Term.denote]
    | .neg  t         =>
      simp[Term.denote]
      simp only [Term.signature] at hA
      apply Subst.admissible_adjoint.term hA hS
    | .plus x y
    | .times x y =>
      simp[Term.denote]
      simp only [Term.signature] at hA
      apply Subst.admissible_symbol_union.mp at hA
      congr 1
      . exact Subst.admissible_adjoint.term hA.1 hS
      . exact Subst.admissible_adjoint.term hA.2 hS
    | .applyFn f args =>
      match f with
        | .num _ => simp[Term.denote]
        | .sym f =>
          simp[Term.denote]
          simp only [Term.signature] at hA
          apply Subst.admissible_symbol_union.mp at hA
          have : σ.adjoint i v (Symbol.Function f)
               = σ.adjoint i w (Symbol.Function f):= by
              simp[Subst.adjoint]
              congr
              funext x
              apply Term.coincidence
              and_intros
              .
                apply Set.EqOn.mono
                . exact Subst.admissible_get_fn_subset f (by simp[Function.signature]) hA.1
                . assumption
              . simp
          simp[this]

          have : ∀ (x : Fin f.arity), Term.denote (σ.adjoint i v) μ args.toVector[x]
                                    = Term.denote (σ.adjoint i w) μ args.toVector[x] := by
            intro x
            apply Subst.admissible_adjoint.term
            .
              apply Subst.admissible_symbol_subset
              . exact TermVector.signature_elem
              . exact hA.2
            . exact hS
          simp_all
    | Term.differential t =>
      simp[Term.denote]
      simp only [Term.signature] at hA
      have : ∀ (x : t.freeVars) (y : ℝ), Term.denote (Subst.adjoint σ i v) (μ.update x y) t
                                       = Term.denote (Subst.adjoint σ i w) (μ.update x y) t :=
        fun _ _ ↦ Subst.admissible_adjoint.term hA hS
      simp_all
decreasing_by
  all_goals try decreasing_trivial
  -- TODO automate this?
  have ha : sizeOf args.toVector[x] < sizeOf args := by
    apply TermVector.sizeOf_lt_of_mem
    simp[TermVector.mem_toVector_iff]

  have hb : sizeOf args < sizeOf (Term.applyFn (Fn.sym f) args) := by simp

  decreasing_trivial

mutual

theorem Subst.admissible_adjoint.formula {v w : State}
                                         {σ : Subst}
                                         {i : Interpretation}
                                         {Φ : Formula}
                                         {U : FCSet Assignable}
                                         (hA : Subst.admissible σ U Φ.signature)
                                         (hS : State.isEqOn v w Uᶜ)
                                         : Formula.denote (Subst.adjoint σ i v) Φ
                                         = Formula.denote (Subst.adjoint σ i w) Φ := by
  match Φ with
    | .True
    | .False => simp[Formula.denote]
    | .applyPred p args =>
      simp only [Formula.signature] at hA
      apply Subst.admissible_symbol_union.mp at hA
      simp[Formula.denote]
      congr
      funext μ

      have : Subst.adjoint σ i v (Symbol.Predicate p)
           = Subst.adjoint σ i w (Symbol.Predicate p) := by
        simp[Subst.adjoint]
        funext args
        simp
        apply Iff.intro
        all_goals
          apply Formula.coincidence
          and_intros
          .
            apply Set.EqOn.symm
            first
              | apply Set.EqOn.mono _ hS
              | apply Set.EqOn.mono _ (Set.EqOn.symm hS)
            exact Subst.admissible_get_pred_subset p (by simp) hA.1
          . simp

      have : ∀ (n : Fin p.arity), Term.denote (σ.adjoint i v) μ args.toVector[n]
                                = Term.denote (σ.adjoint i w) μ args.toVector[n] := by
        intros n
        apply Subst.admissible_adjoint.term
        .
          apply Subst.admissible_symbol_subset
          . exact TermVector.signature_elem
          . exact hA.2
        . exact hS
      simp_all
    | .eq t₁ t₂
    | .gte t₁ t₂ =>
      apply Subst.admissible_symbol_union.mp at hA
      have : ∀ (μ : State), Term.denote (σ.adjoint i v) μ t₁ = Term.denote (σ.adjoint i w) μ t₁ :=
        fun μ ↦Subst.admissible_adjoint.term hA.1 hS
      have : ∀ (μ : State), Term.denote (σ.adjoint i v) μ t₂ = Term.denote (σ.adjoint i w) μ t₂ :=
        fun μ ↦Subst.admissible_adjoint.term hA.2 hS
      simp_all[Formula.denote]
    | .not Φ' =>
      simp[Formula.denote]
      simp only [Formula.signature] at hA
      exact Subst.admissible_adjoint.formula hA hS
    | .and Φ₁ Φ₂ =>
      simp[Formula.denote]
      simp only [Formula.signature] at hA
      apply Subst.admissible_symbol_union.mp at hA
      congr 1
      . exact Subst.admissible_adjoint.formula hA.1 hS
      . exact Subst.admissible_adjoint.formula hA.2 hS
    | .forall x Φ'
    | .exists x Φ' =>
      simp only [Formula.signature] at hA
      have : Formula.denote (σ.adjoint i v) Φ' = Formula.denote (σ.adjoint i w) Φ' :=
        Subst.admissible_adjoint.formula hA hS
      simp_all[Formula.denote]
    | .diamond α Φ'
    | .box α Φ' =>
      simp only [Formula.signature] at hA
      apply Subst.admissible_symbol_union.mp at hA
      have : Program.denote (σ.adjoint i v) α = Program.denote (σ.adjoint i w) α :=
        Subst.admissible_adjoint.program hA.1 hS
      have : Formula.denote (σ.adjoint i v) Φ' = Formula.denote (σ.adjoint i w) Φ' :=
        Subst.admissible_adjoint.formula hA.2 hS
      simp_all[Formula.denote]
    | .ref α β =>
      simp only [Formula.signature] at hA
      apply Subst.admissible_symbol_union.mp at hA
      have : Program.denote (σ.adjoint i v) α = Program.denote (σ.adjoint i w) α :=
        Subst.admissible_adjoint.program hA.1 hS
      have : Program.denote (σ.adjoint i v) β = Program.denote (σ.adjoint i w) β :=
        Subst.admissible_adjoint.program hA.2 hS
      simp_all[Formula.denote]
termination_by
  Φ.size
decreasing_by
  all_goals simp[Formula.size]
  all_goals omega

theorem Subst.admissible_adjoint.program {v w : State}
                                         {σ : Subst}
                                         {i : Interpretation}
                                         {α : Program}
                                         {U : FCSet Assignable}
                                         (hA : Subst.admissible σ U α.signature)
                                         (hS : State.isEqOn v w Uᶜ)
                                         : Program.denote (Subst.adjoint σ i v) α
                                         = Program.denote (Subst.adjoint σ i w) α := by
  match α with
    | .const a =>
      simp[Program.denote, Subst.adjoint]
    | .assign x t =>
      simp only [Program.signature] at hA
      have : ∀ (μ : State), Term.denote (σ.adjoint i v) μ t = Term.denote (σ.adjoint i w) μ t := by
        intros μ
        apply Subst.admissible_adjoint.term hA hS
      simp_all[Program.denote]
    | .random x =>
      simp only [Program.denote]
    | .test Φ =>
      simp[Program.denote]
      simp only [Program.signature] at hA
      have : Formula.denote (σ.adjoint i v) Φ = Formula.denote (σ.adjoint i w) Φ :=
        Subst.admissible_adjoint.formula hA hS
      simp_all
    | .ode system Ψ =>
      simp[Program.denote]
      have : Formula.denote (σ.adjoint i v) (odeEvolutionFormula system Ψ)
           = Formula.denote (σ.adjoint i w) (odeEvolutionFormula system Ψ) := by
        apply Subst.admissible_adjoint.formula
        .
          rw[ode_evolution_formula_signature_eq_ode_signature]
          exact hA
        . exact hS
      simp_all
    | .choice α β
    | .seq α β =>
      simp only [Program.signature] at hA
      apply Subst.admissible_symbol_union.mp at hA
      have := Subst.admissible_adjoint.program (i := i) (α := α) hA.1 hS
      have := Subst.admissible_adjoint.program (i := i) (α := β) hA.2 hS
      simp_all[Program.denote]
    | .loop α =>
      simp only [Program.signature] at hA
      have := Subst.admissible_adjoint.program (i := i) (α := α) hA hS
      simp_all[Program.denote]
termination_by
  α.size
decreasing_by
  all_goals simp[Program.size]
  all_goals try omega
  simp[ode_evolution_formula_size_bound, *]

end

/- Substitution preserves ode's assignables -/
lemma ode_mapM_assignables_eq
  {σ : Subst}
  {U : FCSet Assignable}
  {system : OdeSystem}
  {ssystem : OdeSystem}
  (h : system.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ U x.term))
       = some ssystem)
  : OdeSystem.assignables ssystem = OdeSystem.assignables system := by
  unfold OdeSystem.assignables at *;
  induction system generalizing ssystem <;> simp_all +decide [ List.mapM_cons ];
  cases h' : Term.applySubst σ U ‹ODE›.term <;> simp_all +decide [ Option.bind_eq_some_iff ];
  aesop

/- `Program.substBoundVars` computes the bound variables of the substituted program -/
lemma Program.substBoundVars_applySubst_boundVars
  (σ : Subst)
  (U V : FCSet Assignable)
  (α α' : Program) :
  Program.applySubst σ U α = some ⟨V,α'⟩ → α'.boundVars' = α.substBoundVars σ := by
  intro h
  match α with
  | .const _
  | .test _
  | .assign _ _
  | .random _ =>
    simp[Program.applySubst, Option.bind] at h
    grind only [substBoundVars, boundVars']
  | .choice β γ
  | .seq β γ =>
    simp[Program.applySubst, Option.bind] at h
    split at h
    . contradiction
    simp only at h
    split at h
    . contradiction
    simp at h
    next β' hβ _ _ γ' hγ =>
      apply Program.substBoundVars_applySubst_boundVars at hγ
      apply Program.substBoundVars_applySubst_boundVars at hβ
      grind only [substBoundVars, boundVars', = Set.subset_def, = Set.mem_union]
  | .loop β =>
    simp[Program.applySubst, Option.bind] at h
    split at h
    . contradiction
    simp at h
    next β' hβ =>
      apply Program.substBoundVars_applySubst_boundVars at hβ
      grind only [substBoundVars, boundVars', = Set.subset_def, = Set.mem_union]
  | .ode sys _ =>
    simp[Program.applySubst, Option.bind] at h
    split at h
    . contradiction
    simp only at h
    split at h
    . contradiction
    simp at h
    next sys' hsys =>
      have hassign : OdeSystem.assignables sys' = OdeSystem.assignables sys :=
          ode_mapM_assignables_eq (show _ = some sys' from ‹_›)
      grind only [substBoundVars, boundVars', FCSet.to_set_eq, = Set.subset_def, = Set.mem_union, = Finset.mem_coe,
        = Set.mem_image, = Finset.mem_map]

/- Weakening the taboo does not create clash. -/
mutual

lemma TermVector.taboo_mono {σ : Subst} {U V : FCSet Assignable} {n : ℕ} {ts ts' : TermVector n} :
  V.toSet ⊆ U.toSet → ts.applySubst σ U = ts' → ts.applySubst σ V = ts' := by
  match n with
  | 0 => match ts with
    | .nil =>
      simp_all[TermVector.applySubst]
  | n+1 => match ts with
    | .cons t ts' =>
      simp_all[TermVector.applySubst, Option.bind_eq_some_iff]
      intro hUV _ h₁ _ h₂
      have := Term.taboo_mono hUV h₁
      have := TermVector.taboo_mono hUV h₂
      grind only

lemma Term.taboo_mono {σ : Subst} {U V : FCSet Assignable} {t t' : Term} :
  V.toSet ⊆ U.toSet → t.applySubst σ U = t' → t.applySubst σ V = t' := by
  match t with
  | .var _
  | .applyFn (Fn.num _) _
  | .differential _ =>
    grind only [Term.applySubst]
  | .neg _ =>
    simp[Term.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h
    have := Term.taboo_mono hUV h
    grind only
  | .plus _ _
  | .times _ _ =>
    simp[Term.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h₁ _ h₂
    have := Term.taboo_mono hUV h₁
    have := Term.taboo_mono hUV h₂
    grind only
  | .applyFn (Fn.sym _) _ =>
    simp[Term.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h₁ h₂
    apply TermVector.taboo_mono hUV at h₁
    split at h₂
    . simp_all[Option.bind]
      split at h₂
      . contradiction
      simp_all
      suffices (↑(Term.freeVars (σ.get (Symbol.Function _))) ∩ V.toSet = ∅) by
        rw[this]
        simp
      grind only [= Set.subset_def, = Set.mem_inter_iff, = Set.mem_empty_iff_false]
    . simp_all
end

lemma ode_mapM_taboo_mono {σ : Subst} {U V : FCSet Assignable} {sys sys' : OdeSystem} :
  V.toSet ⊆ U.toSet →
  sys.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ U x.term)) = some sys' →
  sys.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ V x.term)) = some sys' := by
  match sys with
  | .nil =>
    simp_all
  | .cons _ _ =>
    simp_all[Option.bind_eq_some_iff]
    intro hUV _ h₁ _ h₂
    have := Term.taboo_mono hUV h₁
    have := ode_mapM_taboo_mono hUV h₂
    simp_all only [Option.pure_def, Option.bind_eq_bind, Option.some.injEq, exists_eq_left',
      implies_true]

mutual
lemma Formula.taboo_mono {σ : Subst} {U V : FCSet Assignable} {φ ψ : Formula} :
  V.toSet ⊆ U.toSet → φ.applySubst σ U = ψ → φ.applySubst σ V = ψ := by
  match φ with
  | .True
  | .False =>
    grind only [Formula.applySubst]
  | .gte _ _
  | .eq _ _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h₁ _ h₂
    have := Term.taboo_mono hUV h₁
    have := Term.taboo_mono hUV h₂
    grind only
  | .not _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h
    have := Formula.taboo_mono hUV h
    grind only
  | .exists x _
  | .forall x _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h
    have : ({.var x} ∪ V).toSet ⊆ ({.var x} ∪ U).toSet := by
      grind only [= Set.subset_def, FCSet.to_set_union, = Set.mem_union]
    apply Formula.taboo_mono this at h
    grind only
  | .and _ _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h₁ _ h₂
    have := Formula.taboo_mono hUV h₁
    have := Formula.taboo_mono hUV h₂
    grind only
  | .box α _
  | .diamond α _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV W _ h₁ _ h₂
    have := Program.taboo_mono hUV h₁
    have : α.substBoundVars σ ∪ U = W := by
      have := Program.taboo_mono (Set.Subset.refl _) h₁
      grind only
    rw[←this] at h₂
    have : (α.substBoundVars σ ∪ V).toSet ⊆ (α.substBoundVars σ ∪ U).toSet := by
      grind only [= Set.subset_def, FCSet.to_set_union, = Set.mem_union]
    have := Formula.taboo_mono this h₂
    grind only [FCSet.to_set_union, = Set.mem_union]
  | .ref _ _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV _ _ h₁ _ _ h₂
    have := Program.taboo_mono hUV h₁
    have := Program.taboo_mono hUV h₂
    grind only
  | .applyPred _ _ =>
    simp[Formula.applySubst, Option.bind_eq_some_iff]
    intro hUV _ h₁ h
    have := TermVector.taboo_mono hUV h₁
    split at h
    . simp_all[Option.bind]
      split at h
      . contradiction
      simp_all
      suffices (↑(Formula.freeVars' (σ.get (Symbol.Predicate _))) ∩ V.toSet = ∅) by
        rw[this]
        simp
      grind only [= Set.subset_def, = Set.mem_inter_iff, = Set.mem_empty_iff_false]
    . simp_all

lemma Program.taboo_mono {σ : Subst} {U V W: FCSet Assignable} {α β : Program} :
  V.toSet ⊆ U.toSet → α.applySubst σ U = some ⟨W, β⟩ → α.applySubst σ V = some ⟨α.substBoundVars σ ∪ V, β⟩ := by
  match α with
  | .const _
  | .random _ =>
    grind only [Program.applySubst, Program.substBoundVars, = Option.pure_apply]
  | .test _ =>
    simp[Program.applySubst, Program.substBoundVars, Option.bind_eq_some_iff]
    intro hUV _ h
    have := Formula.taboo_mono hUV h
    grind only
  | .assign _ _ =>
    simp[Program.applySubst, Program.substBoundVars, Option.bind_eq_some_iff]
    intro hUV _ h
    have := Term.taboo_mono hUV h
    grind only
  | .choice _ _ =>
    simp[Program.applySubst, Program.substBoundVars, Option.bind_eq_some_iff]
    intro hUV _ _ h₁ _ _ h₂
    have := Program.taboo_mono hUV h₁
    have := Program.taboo_mono hUV h₂
    grind only [FCSet.to_set_union, = Set.mem_union]
  | .seq α _ =>
    simp[Program.applySubst, Program.substBoundVars, Option.bind_eq_some_iff]
    intro hUV W _ h₁ _ _ h₂
    have := Program.taboo_mono hUV h₁
    have : α.substBoundVars σ ∪ U = W := by
      have := Program.taboo_mono (Set.Subset.refl _) h₁
      grind only
    rw[←this] at h₂
    have : (α.substBoundVars σ ∪ V).toSet ⊆ (α.substBoundVars σ ∪ U).toSet := by
      grind only [= Set.subset_def, FCSet.to_set_union, = Set.mem_union]
    have := Program.taboo_mono this h₂
    grind only [FCSet.to_set_union, = Set.mem_union]
  | .loop α =>
    simp[Program.applySubst, Program.substBoundVars, Option.bind_eq_some_iff]
    intro hUV _ _ h₁ _ h₂
    have : (α.substBoundVars σ ∪ V).toSet ⊆ (α.substBoundVars σ ∪ U).toSet := by
      grind only [= Set.subset_def, FCSet.to_set_union, = Set.mem_union]
    have := Program.taboo_mono this h₁
    grind only [FCSet.to_set_union, = Set.mem_union]
  | .ode sys _ =>
    simp[Program.applySubst, Program.substBoundVars, Option.bind_eq_some_iff, -FCSet.to_set_eq]
    intro  hUV _ h₁ _ h₂
    set BV := FCSet.Finite (sys.assignables ∪ Finset.map Assignable.diff_emb sys.assignables)
    have hUV' : (BV ∪ V).toSet ⊆ (BV ∪ U).toSet := by
      grind only [= Set.subset_def, FCSet.to_set_union, = Set.mem_union]
    have := Formula.taboo_mono hUV' h₁
    have := ode_mapM_taboo_mono hUV' h₂
    simp_all[BV, Program.boundVars']

end

/- Corollary: USubst updated taboo coincides with `Program.substBoundVars`. -/
theorem Program.substBoundVars_applySubst {σ : Subst} {α α' : Program} {U V : FCSet Assignable} :
  α.applySubst σ U = some ⟨V, α'⟩ → α.substBoundVars σ ∪ U = V := by
  intro h
  have := Program.taboo_mono (Set.Subset.refl _) h
  grind only

/- Corollary: applySubst's output is unique (w.r.t the taboo), as long as it does not clash. -/

lemma TermVector.applySubst_unique {σ : Subst} {U V : FCSet Assignable} {n : ℕ} {ts ts₁ ts₂ : TermVector n} :
  ts.applySubst σ U = ts₁ → ts.applySubst σ V = ts₂ → ts₁ = ts₂ := by
  intro h₁ h₂
  obtain ⟨hU,hV⟩ : (U ∩ V).toSet ⊆ U.toSet ∧ (U ∩ V).toSet ⊆ V.toSet := by
    grind only [= Set.subset_def, FCSet.to_set_inter, = Set.mem_inter_iff]
  apply TermVector.taboo_mono hU at h₁
  apply TermVector.taboo_mono hV at h₂
  grind only

lemma Term.applySubst_unique {σ : Subst} {U V : FCSet Assignable} {t t₁ t₂ : Term} :
  t.applySubst σ U = t₁ → t.applySubst σ V = t₂ → t₁ = t₂ := by
  intro h₁ h₂
  obtain ⟨hU,hV⟩ : (U ∩ V).toSet ⊆ U.toSet ∧ (U ∩ V).toSet ⊆ V.toSet := by
    grind only [= Set.subset_def, FCSet.to_set_inter, = Set.mem_inter_iff]
  apply Term.taboo_mono hU at h₁
  apply Term.taboo_mono hV at h₂
  grind only


lemma ode_mapM_applySubst_unique {σ : Subst} {U V : FCSet Assignable} {sys sys₁ sys₂ : OdeSystem} :
  sys.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ U x.term)) = some sys₁ →
  sys.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ V x.term)) = some sys₂ →
  sys₁ = sys₂ := by
  intro h₁ h₂
  obtain ⟨hU,hV⟩ : (U ∩ V).toSet ⊆ U.toSet ∧ (U ∩ V).toSet ⊆ V.toSet := by
    grind only [= Set.subset_def, FCSet.to_set_inter, = Set.mem_inter_iff]
  apply ode_mapM_taboo_mono hU at h₁
  apply ode_mapM_taboo_mono hV at h₂
  grind only

lemma Formula.applySubst_unique {σ : Subst} {U V : FCSet Assignable} {φ ψ₁ ψ₂ : Formula} :
  φ.applySubst σ U = ψ₁ → φ.applySubst σ V = ψ₂ → ψ₁ = ψ₂ := by
  intro h₁ h₂
  obtain ⟨hU,hV⟩ : (U ∩ V).toSet ⊆ U.toSet ∧ (U ∩ V).toSet ⊆ V.toSet := by
    grind only [= Set.subset_def, FCSet.to_set_inter, = Set.mem_inter_iff]
  apply Formula.taboo_mono hU at h₁
  apply Formula.taboo_mono hV at h₂
  grind only

lemma Program.applySubst_unique {σ : Subst} {U V W₁ W₂ : FCSet Assignable} {α β₁ β₂ : Program} :
  α.applySubst σ U = some ⟨W₁, β₁⟩ → α.applySubst σ V = some ⟨W₂, β₂⟩ → β₁ = β₂ := by
  intro h₁ h₂
  obtain ⟨hU,hV⟩ : (U ∩ V).toSet ⊆ U.toSet ∧ (U ∩ V).toSet ⊆ V.toSet := by
    grind only [= Set.subset_def, FCSet.to_set_inter, = Set.mem_inter_iff]
  apply Program.taboo_mono hU at h₁
  apply Program.taboo_mono hV at h₂
  grind only

end Theorems
