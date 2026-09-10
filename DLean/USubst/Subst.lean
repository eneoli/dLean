import DLean.Syntax.Definitions
import DLean.Semantics.Interpretation
import DLean.Util.FCSet
import DLean.Semantics.FreeVariables
import DLean.Semantics.BoundVariables

open Semantics

inductive SubstEntry : Type where
  | fn : (f : FunctionSymbol) → Term → SubstEntry
  -- Taboo condition checked when creating the substitution required for defining `Subst.adjoint`
  | unitFun : (F : UnitFunctional) → (t : Term)
            → (FCSet.Finite F.taboo.toFinset) ∩ t.freeVars' = ∅  → SubstEntry
  | pred : (p : PredicateSymbol) → Formula → SubstEntry
  -- Taboo condition checked when creating the substitution required for defining `Subst.adjoint`
  | unitPred : (P : UnitPredicational) → (f : Formula)
            → (FCSet.Finite P.taboo.toFinset) ∩ f.freeVars' = ∅  → SubstEntry
  | prog : (a : ProgramSymbol) → Program → SubstEntry

def SubstEntry.symbol : SubstEntry → Symbol
  | .fn f _         => .Function f
  | .unitFun F _ _  => .UnitFun F
  | .pred p _       => .Predicate p
  | .unitPred P _ _ => .UnitPred P
  | .prog a _       => .Program a


def Subst.Nodup (σ : List SubstEntry) : Prop :=
  (σ.map SubstEntry.symbol).Nodup

def Subst : Type := { σ : List SubstEntry // Subst.Nodup σ }

theorem Subst.tail_nodup {e : SubstEntry}
                         {σ : List SubstEntry}
                         : Subst.Nodup (e::σ) → Subst.Nodup σ := by
  simp[Subst.Nodup]

def Symbol.SubstType : Symbol → Type
  | .Function _ | .UnitFun _ => Term
  | .Predicate _ | .UnitPred _ => Formula
  | .Program _ => _root_.Program

def SubstEntry.rhs (e : SubstEntry) : e.symbol.SubstType :=
  match e with
    | .fn _ rhs | .unitFun _ rhs _ => rhs
    | .pred _ rhs | .unitPred _ rhs _ => rhs
    | .prog _ rhs => rhs

def Symbol.default : (symbol : Symbol) → symbol.SubstType
  | .Function f  => Term.applyFn (.sym f) (Term.dots f.arity)
  | .UnitFun F   => Term.unit F
  | .Predicate p => Formula.applyPred p (Term.dots p.arity)
  | .UnitPred P  => Formula.unit P
  | .Program a   => Program.const a

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

lemma TermVector.toSubstAux_in {n k : ℕ} (ts : TermVector n) (s : Symbol) (hs : Subst.Nodup (ts.toSubstAux k)) :
  Subst.mem ⟨ts.toSubstAux k, hs⟩ s ↔ ∃ m < n, s = .Function (.dot (m + k)) := by
  match n,ts with
  | 0,.nil =>
    simp[TermVector.toSubstAux, Subst.mem]
  | n+1,.cons _ _ =>
    simp only [toSubstAux, Subst.mem, SubstEntry.symbol, Order.lt_add_one_iff]
    apply Iff.intro
    . rintro (h|h)
      . exact ⟨0, Nat.zero_le _, by simp only [zero_add,h]⟩
      . rw[TermVector.toSubstAux_in] at h
        rcases h with ⟨_,_⟩
        simp_all only [Symbol.Function.injEq, FunctionSymbol.dot.injEq]
        grind only
    rintro ⟨m,_⟩
    simp_all only [Symbol.Function.injEq, FunctionSymbol.dot.injEq, Nat.add_eq_right,
      TermVector.toSubstAux_in]
    match m with
    | 0 => exact Or.inl rfl
    | m+1 => grind only

theorem TermVector.toSubst_in {n : ℕ} (ts : TermVector n) (s : Symbol) :
  s ∈ ts.toSubst ↔ ∃ m < n, s = .Function (.dot m) := TermVector.toSubstAux_in _ _ _


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

def TermVector.applySubst {n : ℕ} (σ : Subst) (U : FCSet Variable) (ts : TermVector n) : Option (TermVector n) :=
  match ts with
    | .nil => pure .nil
    | .cons t ts => do
      return .cons (← Term.applySubst σ U t) (← TermVector.applySubst σ U ts)
termination_by (σ.size, sizeOf ts)
decreasing_by
all_goals simp_wf
all_goals grind only [= Prod.lex_def]


def Term.applySubst (σ : Subst) (U : FCSet Variable) (t : Term) : Option Term :=
  match t with
    | .var x  => return .var x
    | .neg t' => do return .neg (← Term.applySubst σ U t')
    | .plus t₁ t₂ => do return .plus (← Term.applySubst σ U t₁) (← Term.applySubst σ U t₂)
    | .times t₁ t₂ => do return .times (← Term.applySubst σ U t₁) (← Term.applySubst σ U t₂)
    | .differential t => do
        return .differential (← Term.applySubst σ .univ t)
    | .unit F => do
        return Subst.get σ F
    | .applyFn (.num _) _ => do
        return t
    | .applyFn (.sym f) args => do
        let sargs ← TermVector.applySubst σ U args
        if (.Function f) ∈ σ then
          guard <| (Subst.get σ f).freeVars' ∩ U = ∅
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
def Program.substBoundVars (σ : Subst) (α : Program) : FCSet Variable :=
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

def Formula.applySubst (σ : Subst) (U : FCSet Variable) (Φ : Formula) : Option Formula := match Φ with
  | .True
  | .False            => Φ
  | .eq t₁ t₂         => do return .eq (← t₁.applySubst σ U) (← t₂.applySubst σ U)
  | .gte t₁ t₂        => do return .gte (← t₁.applySubst σ U) (← t₂.applySubst σ U)
  | .not Φ'           => do return .not (← Φ'.applySubst σ U)
  | .and Φ₁ Φ₂        => do return .and (← Φ₁.applySubst σ U) (← Φ₂.applySubst σ U)
  | .forall x Φ       => do
      return .forall x (← Φ.applySubst σ ({x} ∪ U))
  | .exists x Φ       => do
      return .exists x (← Φ.applySubst σ ({x} ∪ U))
  | .diamond α Φ      => do
      let ⟨V,σα⟩ ← α.applySubst σ U
      return .diamond σα (← Φ.applySubst σ V)
  | .box α Φ          => do
      let ⟨V,σα⟩ ← α.applySubst σ U
      return .box σα (← Φ.applySubst σ V)
  | .ref α β          => do
      return .ref (← α.applySubst σ U).2 (← β.applySubst σ U).2
  | .unit P => do
    return Subst.get σ P
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

def Program.applySubst (σ : Subst) (U : FCSet Variable) (α : Program) : Option (FCSet Variable × Program) := match α with
  | .assign x t   => return ⟨{x} ∪ U, .assign x (← t.applySubst σ U)⟩
  | .random x     => return ⟨{x} ∪ U, .random x⟩
  | .test Φ       => return ⟨U, .test (← Φ.applySubst σ U)⟩
  | .ode system Ψ => do
    let vars := system.variables
    let vars' := vars.map Variable.diff_emb
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

section Theorems

/- Lemmas about `Subst.get` -/

lemma Subst.notin_default (σ : Subst) (s : Symbol) : s ∉ σ → σ.get s = s.default := by
  match σ with
    | ⟨.nil, _⟩ => simp[Subst.get]
    | ⟨e::σ', h⟩ =>
      simp_all only [Membership.mem, mem, not_or, get, ↓reduceDIte, and_imp]
      exact fun _ h ↦ Subst.notin_default _ _ h
termination_by
  σ.1

lemma Subst.get_unitfun_head {σ : Subst}
                             {F : UnitFunctional}
                             {rhs : Term}
                             {hdis : FCSet.Finite F.taboo.toFinset ∩ rhs.freeVars' = ∅}
                             {h : Subst.Nodup (.unitFun F rhs hdis :: σ.1)}
                             : Subst.get ⟨.unitFun F rhs hdis :: σ.1, h⟩ (Symbol.UnitFun F) = rhs := by
  simp[Subst.get, SubstEntry.symbol, SubstEntry.rhs]

lemma Subst.get_pred_head {σ : Subst}
                          {p : PredicateSymbol}
                          {rhs : Formula}
                          {h : Subst.Nodup (.pred p rhs :: σ.1)}
                          : Subst.get ⟨.pred p rhs :: σ.1, h⟩ (Symbol.Predicate p) = rhs := by
  simp[Subst.get, SubstEntry.symbol, SubstEntry.rhs]

lemma Subst.get_unitpred_head {σ : Subst}
                              {P : UnitPredicational}
                              {rhs : Formula}
                              {hdis : FCSet.Finite P.taboo.toFinset ∩ rhs.freeVars' = ∅}
                              {h : Subst.Nodup (.unitPred P rhs hdis :: σ.1)}
                              : Subst.get ⟨.unitPred P rhs hdis :: σ.1, h⟩ (Symbol.UnitPred P) = rhs := by
  simp[Subst.get, SubstEntry.symbol, SubstEntry.rhs]

lemma Subst.get_unitPred_freeVars (σ : Subst) (P : UnitPredicational) : Disjoint (σ.get (.UnitPred P)).freeVars P.taboo.toFinset := by
  match σ with
  | ⟨.nil, _⟩ =>
    simp[Subst.get, Formula.freeVars, Symbol.default]
    exact Set.disjoint_compl_left_iff_subset.mpr fun ⦃a⦄ a_1 ↦ a_1
  | ⟨e::σ', h⟩ =>
    set σ' : Subst := ⟨σ', Subst.tail_nodup h⟩
    match decEq (Symbol.UnitPred P) e.symbol with
    | .isFalse _ =>
      simp_all only [get, ↓reduceDIte]
      apply Subst.get_unitPred_freeVars
    | .isTrue h' =>
      match e with
      | .unitPred P f hdis =>
        simp[SubstEntry.symbol] at h'
        rw[h', Subst.get_unitpred_head (σ:=σ')]
        rw[Set.disjoint_iff_inter_eq_empty, Formula.free_vars_decidable]
        simp[-List.coe_toFinset] at hdis
        grind only
termination_by
  σ.1

-- Lemmas about `Subst.get` for `TermVector.toSubst`

theorem term_vector_to_subst_get.fn
  {n : ℕ}
  {args : TermVector n}
  {f : String}
  {a : ℕ}
  : Subst.get args.toSubst (Symbol.Function (FunctionSymbol.udef f a))
  = Symbol.default (FunctionSymbol.udef f a) := by
  apply Subst.notin_default
  rw[TermVector.toSubst_in]
  simp

theorem term_vector_to_subst_get.pred
  {n : ℕ}
  {args : TermVector n}
  {p : PredicateSymbol}
  : Subst.get args.toSubst (.Predicate p)
  = Formula.applyPred p (Term.dots p.arity) := by
  apply Subst.notin_default
  rw[TermVector.toSubst_in]
  simp

theorem term_vector_to_subst_get.unitpred
  {n : ℕ}
  {args : TermVector n}
  {P : UnitPredicational}
  : Subst.get args.toSubst (.UnitPred P)
  = Formula.unit P := by
  apply Subst.notin_default
  rw[TermVector.toSubst_in]
  simp

theorem term_vector_to_subst_get.program
  {n : ℕ}
  {args : TermVector n}
  {a : ProgramSymbol}
  : Subst.get args.toSubst (.Program a)
  = Program.const a := by
  apply Subst.notin_default
  rw[TermVector.toSubst_in]
  simp

theorem term_vector_to_subst_get.unitfun
  {n : ℕ}
  {args : TermVector n}
  {F : UnitFunctional}
  : Subst.get args.toSubst (.UnitFun F)
  = Term.unit F := by
  apply Subst.notin_default
  rw[TermVector.toSubst_in]
  simp

theorem term_vector_to_subst_get.dot.mem
  {n : ℕ}
  (args : TermVector n)
  (k : ℕ)
  (m : ℕ)
  (h₁ : m ≥ k)
  (h₂ : m < n + k)
  (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (Symbol.Function (FunctionSymbol.dot m))
  = args.toVector[m - k] := by
  cases args with
    | nil => grind
    | cons a as =>
      simp_all [TermVector.toSubstAux, Subst.get]
      split
      .
        next h =>
        cases h
        simp_all[SubstEntry.rhs, TermVector.toVector]
      .
        have : m ≥  k + 1 := by grind[SubstEntry.symbol]
        have := term_vector_to_subst_get.dot.mem as (k + 1) m (by omega) (by omega)
        simp_all [TermVector.toVector]
        grind

theorem term_vector_to_subst_get.dot.nomem
  (m : ℕ)
  {n : ℕ}
  (args : TermVector n)
  (h : m ≥ n)
  : Subst.get args.toSubst (Symbol.Function (FunctionSymbol.dot m))
  = Term.dot m := by
  apply Subst.notin_default
  rw[TermVector.toSubst_in]
  simp_all

/- Substitution preserves ode's variables -/
lemma ode_mapM_variables_eq
  {σ : Subst}
  {U : FCSet Variable}
  {system : OdeSystem}
  {ssystem : OdeSystem}
  (h : system.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ U x.term))
       = some ssystem)
  : OdeSystem.variables ssystem = OdeSystem.variables system := by
  unfold OdeSystem.variables at *;
  induction system generalizing ssystem <;> simp_all +decide [ List.mapM_cons ];
  cases h' : Term.applySubst σ U ‹ODE›.term <;> simp_all +decide [ Option.bind_eq_some_iff ];
  aesop

/- `Program.substBoundVars` computes the bound variables of the substituted program -/
lemma Program.substBoundVars_applySubst_boundVars
  (σ : Subst)
  (U V : FCSet Variable)
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
      have hassign : OdeSystem.variables sys' = OdeSystem.variables sys :=
          ode_mapM_variables_eq (show _ = some sys' from ‹_›)
      grind only [substBoundVars, boundVars', FCSet.to_set_eq, = Set.subset_def, = Set.mem_union, = Finset.mem_coe,
        = Set.mem_image, = Finset.mem_map]

/- Weakening the taboo does not create clash. -/
mutual

lemma TermVector.taboo_mono {σ : Subst} {U V : FCSet Variable} {n : ℕ} {ts ts' : TermVector n} :
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

lemma Term.taboo_mono {σ : Subst} {U V : FCSet Variable} {t t' : Term} :
  V.toSet ⊆ U.toSet → t.applySubst σ U = t' → t.applySubst σ V = t' := by
  match t with
  | .var _
  | .unit _
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
      suffices (↑(Term.freeVars' (σ.get (Symbol.Function _))) ∩ V.toSet = ∅) by
        rw[this]
        simp
      grind only [= Set.subset_def, = Set.mem_inter_iff, = Set.mem_empty_iff_false]
    . simp_all
end

lemma ode_mapM_taboo_mono {σ : Subst} {U V : FCSet Variable} {sys sys' : OdeSystem} :
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
lemma Formula.taboo_mono {σ : Subst} {U V : FCSet Variable} {φ ψ : Formula} :
  V.toSet ⊆ U.toSet → φ.applySubst σ U = ψ → φ.applySubst σ V = ψ := by
  match φ with
  | .True
  | .False
  | .unit P =>
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
    have : ({x} ∪ V).toSet ⊆ ({x} ∪ U).toSet := by
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

lemma Program.taboo_mono {σ : Subst} {U V W: FCSet Variable} {α β : Program} :
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
    set BV := FCSet.Finite (sys.variables ∪ Finset.map Variable.diff_emb sys.variables)
    have hUV' : (BV ∪ V).toSet ⊆ (BV ∪ U).toSet := by
      grind only [= Set.subset_def, FCSet.to_set_union, = Set.mem_union]
    have := Formula.taboo_mono hUV' h₁
    have := ode_mapM_taboo_mono hUV' h₂
    simp_all[BV, Program.boundVars']

end

/- Corollary: USubst updated taboo coincides with `Program.substBoundVars`. -/
theorem Program.substBoundVars_applySubst {σ : Subst} {α α' : Program} {U V : FCSet Variable} :
  α.applySubst σ U = some ⟨V, α'⟩ → α.substBoundVars σ ∪ U = V := by
  intro h
  have := Program.taboo_mono (Set.Subset.refl _) h
  grind only

theorem Program.boundVars_applySubst_subset
  (σ : Subst)
  (U V : FCSet Variable)
  (α α' : Program) :
  Program.applySubst σ U α = some ⟨V,α'⟩ → α'.boundVars ∪ U ⊆ V := by
  intro h
  have := Program.substBoundVars_applySubst h
  apply Program.substBoundVars_applySubst_boundVars at h
  rw[Program.bound_vars_decidable α']
  grind only [= Set.subset_def, FCSet.to_set_union]

theorem Subst.apply_subst_term_vector_to_term
  (σ : Subst)
  (U : FCSet Variable)
  {n : ℕ}
  (args a : TermVector n)
  (x : Fin n)
  : TermVector.applySubst σ U args = some a
  → Term.applySubst σ U args.toVector[x] = some a.toVector[x] := by
    intro h
    cases args with
      | nil => grind
      | cons y ys =>
        simp_all[TermVector.applySubst, Option.bind]
        split at h
        . contradiction
        simp_all
        split at h
        . contradiction
        simp_all

        match x with
          | 0 =>
            rw[← h]
            simp_all[TermVector.toVector]
          | Fin.mk (z + 1) _ =>
            next n _ _ a _ _ _ as _ _ =>
            let z : Fin n := ⟨z, by omega⟩
            have := TermVector.toVector_get_plus_1 y ys z
            simp_all
            rw[this]
            rw[← h]

            have := TermVector.toVector_get_plus_1 a as z
            simp at this
            rw[this]
            apply Subst.apply_subst_term_vector_to_term
            assumption

end Theorems
