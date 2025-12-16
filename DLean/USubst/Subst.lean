import DLean.Syntax.Definitions
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics
import DLean.Semantics.Coincidence
import DLean.Util.FCSet

open Semantics

inductive SubstEntry : Type where
  | fn : (f : FunctionSymbol) → (TermVector f.arity → Term) → SubstEntry
  | pred : (p : PredicateSymbol) → (TermVector p.arity → Formula) → SubstEntry
  | prog : (a : ProgramSymbol) → Program → SubstEntry

def SubstEntry.symbol : SubstEntry → Symbol
  | .fn f _ => .Function f
  | .pred p _ => .Predicate p
  | .prog a _ => .Program a

/-- Decidable version. -/
def SubstEntry.freeVars : SubstEntry → FCSet Assignable
  | .fn f rhs => rhs (Term.dots f.arity) |> Term.freeVars |> .Finite
  | .pred p rhs => rhs (Term.dots p.arity) |> Formula.freeVars'
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

/-- Restricts σ on the symbols in S. -/
-- @[reducible]
abbrev Subst.admissible (σ : Subst) (U : FCSet Assignable) (S : Finset Symbol) :=
  (σ.freeVars S) ∩ U = ∅

mutual

def TermVector.applySubst {n : ℕ} (σ : Subst) (ts : TermVector n) : Option (TermVector n) :=
  match ts with
    | .nil => pure .nil
    | .cons t ts => do
      return .cons (← Term.applySubst σ t) (← TermVector.applySubst σ ts)

def Term.applySubst (σ : Subst) (t : Term) : Option Term :=
  match t with
    | .var _  => return t
    | .neg t' => do return .neg (← Term.applySubst σ t')
    | .plus t₁ t₂ => do return .plus (← Term.applySubst σ t₁) (← Term.applySubst σ t₂)
    | .times t₁ t₂ => do return .times (← Term.applySubst σ t₁) (← Term.applySubst σ t₂)
    | .differential t => do
        guard <| σ.admissible .univ t.signature
        return .differential (← Term.applySubst σ t)
    | .applyFn (.num n) args => do
        let sargs ← TermVector.applySubst σ args
        return .applyFn (.num n) sargs
    | .applyFn (.sym f) args => do
        let sargs ← TermVector.applySubst σ args
        Subst.get σ f sargs

end

mutual

def Formula.applySubst (σ : Subst) (Φ : Formula) : Option Formula := match Φ with
  | .True
  | .False            => Φ
  | .eq t₁ t₂         => do return .eq (← t₁.applySubst σ) (← t₂.applySubst σ)
  | .gte t₁ t₂        => do return .gte (← t₁.applySubst σ) (← t₂.applySubst σ)
  | .not Φ'           => do return .not (← Φ'.applySubst σ)
  | .and Φ₁ Φ₂        => do return .and (← Φ₁.applySubst σ) (← Φ₂.applySubst σ)
  | .forall x Φ       => do
      guard <| σ.admissible {.var x} Φ.signature
      return .forall x (← Φ.applySubst σ)
  | .exists x Φ       => do
      guard <| σ.admissible {.var x} Φ.signature
      return .exists x (← Φ.applySubst σ)
  | .diamond α Φ      => do
      let σα ← α.applySubst σ

      guard <| σ.admissible σα.boundVars' Φ.signature
      return .diamond σα (← Φ.applySubst σ)
  | .box α Φ          => do
      let σα ← α.applySubst σ

      guard <| σ.admissible σα.boundVars' Φ.signature
      return .box (← α.applySubst σ) (← Φ.applySubst σ)
  | .ref α β          => do
      return .ref (← α.applySubst σ) (← β.applySubst σ)
  | .applyPred p args => do
      let sargs ← TermVector.applySubst σ args
      Subst.get σ p sargs

def Program.applySubst (σ : Subst) (α : Program) : Option Program := match α with
  | .assign x t   => return .assign x (← t.applySubst σ)
  | .test Φ       => return .test (← Φ.applySubst σ)
  | .ode system Ψ => do
    let vars := (system.map ODE.var).toFinset
    let vars' := vars.map Assignable.diff_emb
    let terms := system.map ODE.term
    let σΨ ← Ψ.applySubst σ

    guard <| σ.admissible (.Finite (vars ∪ vars')) Ψ.signature
    guard <| terms.all (σ.admissible (.Finite (vars ∪ vars')) ∘ Term.signature)

    let ssystem ← system.mapM (fun {var, term} => do return ODE.mk var (← Term.applySubst σ term))
    return .ode ssystem σΨ
  | .choice α β   => return .choice (← α.applySubst σ) (← β.applySubst σ)
  | .seq α β      => do
    let σα ← α.applySubst σ

    guard <| σ.admissible σα.boundVars' β.signature
    return .seq σα (← β.applySubst σ)
  | .loop α       => do
    let σα ← α.applySubst σ

    guard <| σ.admissible σα.boundVars' α.signature
    return .loop σα
  | .const a      => return Subst.get σ a

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

lemma Subst.get_fn_head {σ : Subst}
                        {f : FunctionSymbol}
                        {rhs : TermVector f.arity → Term}
                        {h : Subst.Nodup (.fn f rhs :: σ.1)}
                        : Subst.get ⟨.fn f rhs :: σ.1, h⟩ (Symbol.Function f) = rhs := by
  simp[Subst.get, SubstEntry.symbol, SubstEntry.rhs]

lemma Subst.get_pred_head {σ : Subst}
                          {p : PredicateSymbol}
                          {rhs : TermVector p.arity → Formula}
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

theorem Subst.free_vars_subset_fun {σ : Subst}
                                   {f : FunctionSymbol}
                                   : ((σ.get f (Term.dots f.arity)).freeVars : Set Assignable)
                                   ⊆ σ.freeVars .none := by
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
            simp_all[σ', Subst.freeVars, SubstEntry.freeVars, SubstEntry.rhs]
      .
        have := @Subst.free_vars_tail σ' x hnodup
        have := @Subst.free_vars_subset_fun σ' f
        grind only [= Set.subset_def, = Finset.mem_coe]
termination_by
  σ.1

theorem Subst.free_vars_subset_pred {σ : Subst}
                                    {p : PredicateSymbol}
                                    : ((σ.get p (Term.dots p.arity)).freeVars : Set Assignable)
                                    ⊆ σ.freeVars .none := by
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
            rw[Formula.free_vars_decidable (rhs (Term.dots p.arity))]
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
  intro h
  match σ with
    | ⟨.nil, _⟩ =>
      apply FCSet.to_set_eq.mpr
      simp[Subst.freeVars]
    | ⟨e::σ', hsubst⟩ =>
      have : Subst.admissible ⟨σ', Subst.tail_nodup hsubst⟩ U S₂ := by
        apply Subst.admissible_symbol_subset hs
        exact (Subst.admissible_subst_cons _).mp h |> And.right
      by_cases e.symbol ∈ S₂
      .
        simp_all[Subst.admissible, Subst.freeVars]
        grind
      .
        simp_all[Subst.admissible, Subst.freeVars]
termination_by
  σ.1

theorem Subst.admissible_symbol_union {σ : Subst}
                                      {U : FCSet Assignable}
                                      {A : Finset Symbol}
                                      {B : Finset Symbol}
  : σ.admissible U (A ∪ B) ↔ σ.admissible U A ∧ σ.admissible U B := by
  apply Iff.intro
  .
    intro h
    and_intros
    all_goals
    exact @Subst.admissible_symbol_subset _ _ (A ∪ B) _ (by simp) h
  .
    intro h
    match σ with
      | ⟨.nil, _⟩ => simp[Subst.freeVars]
      | ⟨e :: σ', hsubst⟩ =>
      have hA := (@Subst.admissible_subst_cons ⟨σ', Subst.tail_nodup hsubst⟩ _ _ _ _).mp h.1
      have hB := (@Subst.admissible_subst_cons ⟨σ', Subst.tail_nodup hsubst⟩ _ _ _ _).mp h.2
      have := Subst.admissible_symbol_union.mpr ⟨hA.2, hB.2⟩
      apply (@Subst.admissible_subst_cons ⟨σ', Subst.tail_nodup hsubst⟩ _ _ _ _).mpr
      grind
termination_by
  σ.1

theorem Subst.admissible_get_fn_subset {σ : Subst}
                                       {U : FCSet Assignable}
                                       {S : Finset Symbol}
                                       (f : FunctionSymbol)
                                       (hf : .Function f ∈ S)
                                       (hA : Subst.admissible σ U S)
  : ((Subst.get σ f (Term.dots f.arity)).freeVars : Set _) ⊆ (U : Set Assignable)ᶜ := by
  match σ with
    | ⟨.nil, _⟩ => simp_all[Subst.get, Subst.freeVars, Symbol.default, Term.freeVars]
    | ⟨e :: σ', hsubst⟩ =>
      by_cases hc : .Function f = e.symbol
      .
        match e with
          | .fn f' rhs =>
            have : f' = f := by simp_all[SubstEntry.symbol]
            cases this
            rw[@Subst.get_fn_head ⟨σ', Subst.tail_nodup hsubst⟩ f rhs hsubst]
            simp_all[Subst.freeVars, SubstEntry.freeVars, Subst.admissible]
            apply Set.subset_compl_iff_disjoint_left.mpr
            simp[Disjoint]
            grind
          | .pred _ _
          | .prog _ _ => simp_all[SubstEntry.symbol]
      .
        simp[Subst.get, hc]
        apply Subst.admissible_get_fn_subset f hf
        exact (@Subst.admissible_subst_cons ⟨σ', Subst.tail_nodup hsubst⟩ _ _ _ _).mp hA
          |> And.right
termination_by
  σ.1

theorem Subst.admissible_get_pred_subset {σ : Subst}
                                         {U : FCSet Assignable}
                                         {S : Finset Symbol}
                                         (p : PredicateSymbol)
                                         (hp : .Predicate p ∈ S)
                                         (hA : Subst.admissible σ U S)
  : ((Subst.get σ p (Term.dots p.arity)).freeVars : Set _) ⊆ (U : Set Assignable)ᶜ := by
  match σ with
    | ⟨.nil, _⟩ => simp_all[Subst.get, Subst.freeVars, Symbol.default, Formula.freeVars]
    | ⟨e :: σ', hsubst⟩ =>
      by_cases hc : .Predicate p = e.symbol
      .
        match e with
          | .pred p' rhs =>
            have : p' = p := by simp_all[SubstEntry.symbol]
            cases this
            rw[@Subst.get_pred_head ⟨σ', Subst.tail_nodup hsubst⟩ p rhs hsubst]
            simp_all[Subst.freeVars, SubstEntry.freeVars, Subst.admissible]
            apply Set.subset_compl_iff_disjoint_left.mpr
            simp[Formula.free_vars_decidable, Disjoint]
            grind
          | .fn _ _
          | .prog _ _ => simp_all[SubstEntry.symbol]
      .
        simp[Subst.get, hc]
        apply Subst.admissible_get_pred_subset p hp
        exact (@Subst.admissible_subst_cons ⟨σ', Subst.tail_nodup hsubst⟩ _ _ _ _).mp hA
          |> And.right
termination_by
  σ.1

theorem Subst.adjoint_nil (i : Interpretation)
                          (v : State)
                          {hsubst : Subst.Nodup []}
  : Subst.adjoint ⟨[], hsubst⟩ i v = i := by
  funext s
  simp[Subst.adjoint]
  match s with
    | .Function f =>
      simp[Subst.get, Symbol.default, Term.denote]
      congr
      -- funext
      match hf : f with
        | .dot n =>
          simp_all[FunctionSymbol.arity]
          funext args
          have : args = fun x ↦ Term.denote i v TermVector.nil.toVector[x] :=  by grind
          aesop
        | .udef name arity =>
          funext args
          simp_all[Interpretation.assignDots]
          have : args = fun x ↦
                          Term.denote (i.assignDots args) v (Term.dots (FunctionSymbol.udef name arity).arity).toVector[↑x] := by
            funext n
            simp_all
            sorry

          sorry
    | .Predicate p => sorry
    | .Program a => simp[Subst.get, Symbol.default, Program.denote]

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
        . apply Subst.free_vars_subset_fun
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
        . apply Subst.free_vars_subset_pred
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

-- theorem Subst.term {v : State}
--                    {i : Interpretation}
--                    {σ : Subst}
--                    {t : Term}
--                    : Term.denote i v (t.applySubst σ)
--                    = Term.denote (Subst.adjoint σ i v) v t := by
--   sorry

end Theorems
