import DLean.USubst.Subst
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics
import DLean.Semantics.Coincidence

open Semantics

lemma ode_evolution_formula_applySubst
  {σ : Subst}
  {U : FCSet Variable}
  {system ssystem : OdeSystem}
  {Ψ Ψ' : Formula}
  : Formula.applySubst σ U Ψ = some Ψ'
  → system.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ U x.term)) = some ssystem
  → Formula.applySubst σ U (odeEvolutionFormula system Ψ)
  = some (odeEvolutionFormula ssystem Ψ') := by

  intros h₁ h₂
  induction system generalizing ssystem Ψ Ψ' with
    | nil => simp_all[odeEvolutionFormula]
    | cons head tail ih =>
      cases _ : Term.applySubst σ U head.term
      . simp_all
      .
        simp_all[Option.bind_eq_some_iff]
        simp_all[odeEvolutionFormula, Term.applySubst, Formula.applySubst]
        aesop


/-- Decidable version.
 -- Restricts σ on the symbols contained in S if some. -/
def Subst.freeVarsSem (σ : Subst) (i : Interpretation) (S : Option (Finset Symbol)) : Finset Variable :=
  match σ with
    | ⟨.nil, _⟩ => ∅
    | ⟨e::xs, h⟩ =>
      let σ' : Subst := ⟨xs, Subst.tail_nodup h⟩
      let efreeVarsSem := match e with
      | .fn _ t | .unitFun _ t _ => t.freeVarsSem i
      | _ => ∅
      match S with
        | .none => efreeVarsSem ∪ σ'.freeVarsSem i S
        | .some S =>
          if e.symbol ∈ S then
            efreeVarsSem ∪ σ'.freeVarsSem i S
          else
            σ'.freeVarsSem i S
termination_by
  σ.1

theorem Subst.freeVarsSem_symbol_subset (σ : Subst) (i : Interpretation)
                                       {S₁ : Finset Symbol}
                                       {S₂ : Finset Symbol}
                                       (hs : S₁ ⊆ S₂)
  : Subst.freeVarsSem σ i S₁ ⊆ Subst.freeVarsSem σ i S₂ := by
  intro h
  match σ with
    | ⟨.nil, _⟩ =>
      simp[Subst.freeVarsSem]
    | ⟨e::σ', hsubst⟩ =>
      have : Subst.freeVarsSem ⟨σ', Subst.tail_nodup hsubst⟩ i S₁ ⊆
        Subst.freeVarsSem ⟨σ', Subst.tail_nodup hsubst⟩ i S₂ := by
        apply Subst.freeVarsSem_symbol_subset _ _ hs
      unfold Subst.freeVarsSem
      simp only
      split
      .
        have : e.symbol ∈ S₂ := by grind only [= Finset.subset_iff]
        split
        . simp_all only [Finset.mem_union, ↓reduceIte]
          grind only [= Finset.subset_iff, = Set.subset_def]
        . simp_all only [Finset.mem_union, ↓reduceIte]
          grind only [= Finset.subset_iff, = Set.subset_def]
        . grind only [= Finset.subset_iff, = Finset.mem_union]
      .
        intro
        split
        . grind only [= Finset.subset_iff, = Finset.mem_union]
        . grind only [= Finset.subset_iff]
termination_by
  σ.1

/- Unused -/
theorem Subst.freeVarsSem_symbol_subset_none {σ : Subst}
                                          {i : Interpretation}
                                          {S : Finset Symbol}
  : Subst.freeVarsSem σ i S ⊆ Subst.freeVarsSem σ i none := by
  match σ with
    | ⟨.nil, _⟩ =>
      simp[Subst.freeVarsSem]
    | ⟨e::σ', hsubst⟩ =>
      have := @Subst.freeVarsSem_symbol_subset_none ⟨σ', Subst.tail_nodup hsubst⟩ i S
      unfold Subst.freeVarsSem
      simp only
      split
      . exact Finset.union_subset_union_right this
      . grw[this]
        exact Finset.subset_union_right
termination_by
  σ.1

theorem Subst.freeVarsSem_symbol_union (σ : Subst) (i : Interpretation)
                                    {S₁ : Finset Symbol}
                                    {S₂ : Finset Symbol}
  : Subst.freeVarsSem σ i S₁ ∪ Subst.freeVarsSem σ i S₂ =
    Subst.freeVarsSem σ i (some (S₁ ∪ S₂)) := by
  apply Finset.Subset.antisymm
  .
    have h₁ : σ.freeVarsSem i S₁ ⊆ σ.freeVarsSem i (some (S₁ ∪ S₂)) :=
      Subst.freeVarsSem_symbol_subset _ _ Finset.subset_union_left
    have h₂ : σ.freeVarsSem i S₂ ⊆ σ.freeVarsSem i (some (S₁ ∪ S₂)) :=
      Subst.freeVarsSem_symbol_subset _ _ Finset.subset_union_right
    exact Finset.union_subset h₁ h₂
  .
    intro h
    match σ with
      | ⟨.nil, _⟩ => simp only [freeVarsSem, Finset.notMem_empty, Finset.union_idempotent,
        imp_self]
      | ⟨e :: σ', hsubst⟩ =>
        simp only [Finset.mem_union]
        have := @Subst.freeVarsSem_symbol_union ⟨σ', Subst.tail_nodup hsubst⟩ i S₁ S₂
        unfold Subst.freeVarsSem
        grind only [= Finset.mem_union]
termination_by
  σ.1

theorem Subst.free_vars_sem_subset_fun {σ : Subst}
                                   {f : FunctionSymbol}
                                   {i : Interpretation}
                                   : ((σ.get f).freeVarsSem i : Set Variable)
                                   ⊆ σ.freeVarsSem i (some (Function.signature (Fn.sym f))) := by
  match h : σ with
    | ⟨.nil, _⟩ =>
      simp[Subst.get, Symbol.default, Subst.freeVarsSem, Term.freeVarsSem, Term.dots_free_vars_sem]
    | ⟨.cons x xs, hnodup⟩ =>
      let σ' : Subst := ⟨xs, Subst.tail_nodup hnodup⟩
      simp[Subst.get]
      split
      next h =>
        unfold Subst.freeVarsSem
        simp only [Function.signature, ← h, Finset.mem_singleton, ↓reduceIte]

        match x with
        | .fn f' rhs =>
          simp_all[SubstEntry.symbol, SubstEntry.rhs]
          cases h
          exact Finset.subset_union_left

      .
        unfold Subst.freeVarsSem
        simp only [Function.signature, Finset.mem_singleton]
        split
        . grind only
        . have := @Subst.free_vars_sem_subset_fun σ' f
          simp_all only [Function.signature, SetLike.coe_subset_coe, Finset.le_eq_subset, σ']
termination_by
  σ.1

lemma Subst.get_unitFun_freeVarsSem (σ : Subst) (F : UnitFunctional) (i : Interpretation) : Disjoint ((σ.get (.UnitFun F)).freeVarsSem i) F.taboo.toFinset := by
  match σ with
  | ⟨.nil, _⟩ =>
    simp[Subst.get, Term.freeVarsSem, Symbol.default]
    exact (i (Symbol.UnitFun F)).fst.2
  | ⟨e::σ', h⟩ =>
    set σ' : Subst := ⟨σ', Subst.tail_nodup h⟩
    match decEq (Symbol.UnitFun F) e.symbol with
    | .isFalse _ =>
      simp_all only [get, ↓reduceDIte]
      apply Subst.get_unitFun_freeVarsSem
    | .isTrue h' =>
      match e with
      | .unitFun F' t hdis =>
        simp[SubstEntry.symbol] at h'
        rw[h', Subst.get_unitfun_head (σ:=σ')]
        rw[←Finset.disjoint_coe]
        apply Disjoint.mono_left (Term.freeVarsSem_subset_freeVars _ _)
        apply Disjoint.symm
        rw[Set.disjoint_iff_inter_eq_empty, Term.free_vars_decidable]
        simp at hdis
        simp_all
termination_by
  σ.1

lemma toSubstAux.freeVarsSem_inc {n : ℕ} (args : TermVector n) (i : Interpretation) (S : Option (Finset Symbol)) :
  ∀ k, Subst.freeVarsSem ⟨args.toSubstAux k, (args.toSubstLemma k).1⟩ i S ⊆ args.freeVarsSem i := by
  match args with
    | .nil =>
      simp[TermVector.toSubstAux, Subst.freeVarsSem]
    | .cons e args' =>
      simp[TermVector.toSubstAux]
      unfold Subst.freeVarsSem
      simp only [TermVector.freeVarsSem]
      intro k
      have := toSubstAux.freeVarsSem_inc args' i S (k+1)
      grw[←this]
      split
      . rfl
      . split
        . rfl
        . exact Finset.subset_union_right

theorem toSubst.freeVarsSem_inc {n : ℕ} (args : TermVector n) (i : Interpretation) (S : Option (Finset Symbol)) :
  args.toSubst.freeVarsSem i S ⊆ args.freeVarsSem i := by
  exact toSubstAux.freeVarsSem_inc _ _ _ 0

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
              (Fin f.arity → ℝ) × ({a // a ∈ (∅ : Finset Variable)} → ℝ))) :=
                contDiff_prodMk_left (fun _ ↦ 0)

            exact ContDiff.comp hg hf
        ⟩
      | .UnitFun F =>
        if (.UnitFun F) ∈ σ
        then
          let T := σ.get (.UnitFun F)
          let fv := T.freeVarsSem i
          ⟨⟨fv, σ.get_unitFun_freeVarsSem F i⟩,
          fun s' ↦ T.denote i (State.zero.finUpdate s'), by
            have hg := @Term.contDiff 0 i State.zero (fv) T
            simp at hg
            have hf : ContDiff ℝ ∞ (fun x ↦ (⟨fun _ ↦ 0, x⟩ :
              (Fin 0 → ℝ) × ({a // a ∈ fv} → ℝ))) :=
                contDiff_prodMk_right (fun _ ↦ 0)
            exact ContDiff.comp hg hf
            ⟩
          else
            i (.UnitFun F)
      | .Predicate p =>
        let Φ := σ.get (.Predicate p)
        fun args ↦
          let idots := i.assignDots args
          v ∈ Formula.denote idots Φ
      | .UnitPred P =>
        fun s' ↦ (σ.get (.UnitPred P)).denote i
          (fun x ↦ if h : x ∈ P.taboo.toFinset
            then 0
            else s' ⟨x, h⟩)
      | .Program a =>
          Program.denote i (σ.get a)

end SubstAdjoint

theorem Subst.adjoint_noeffect_nomem
  (i : Interpretation)
  (v : State)
  (e : Symbol)
  {σ : Subst}
  : e ∉ σ
  → (σ.adjoint i v e) = i e := by
  intro h
  simp[Subst.adjoint]
  match e with
  | .Function f =>
    apply Subst.notin_default at h
    simp[h, Symbol.default, Term.denote]

    apply Subtype.ext
    funext args
    simp_all[Interpretation.assignDots]
    split
    .
      next n =>
      simp_all[FunctionSymbol.arity]
      have : (FunctionSymbol.dot n).arity = 0 := by simp_all[FunctionSymbol.arity]

      have : (fun x ↦ Term.denote i v TermVector.nil.toVector[↑x])
            = args := by
          simp_all[TermVector.toVector]
          funext a
          simp_all[FunctionSymbol.arity]
          grind

      cases this

      have : (fun (x : Fin 0) ↦ Term.denote i v TermVector.nil.toVector[↑x])
            = (fun (x : Fin (FunctionSymbol.dot n).arity) ↦
                Term.denote i v TermVector.nil.toVector[x]) := by
            grind
      cases this
      rfl
    .
      have : ∀ (x : Fin f.arity), (Term.dots f.arity).toVector[(↑x : ℕ)]
          = Term.dot x := by
            apply Interpretation.dots_eq
      simp only[this]
      simp[Term.dot, Term.denote, Interpretation.assignDots]

  | .Predicate p =>
    apply Subst.notin_default at h
    simp[h, Symbol.default, Formula.denote]

    have : ∀ (x : Fin p.arity), (Term.dots p.arity).toVector[(↑x : ℕ)]
             = Term.dot x := by
                apply Interpretation.dots_eq

    simp_all[Term.dot, Term.denote, Interpretation.assignDots]
  | .UnitPred P =>
    apply Subst.notin_default at h
    simp[h, Symbol.default, Formula.denote]
    funext s'
    simp[setOf]
    suffices (fun x ↦ if ↑x ∈ P.taboo.toFinset then 0 else s' x) = s' by
      rw[this]
    funext x
    grind only [= Set.mem_compl_iff, = Finset.mem_coe]
  | .Program a =>
    apply Subst.notin_default at h
    simp[h, Symbol.default, Program.denote]
  | .UnitFun F =>
    simp[h]


theorem subst_adjoint_of_term_vector_to_subst
  (i : Interpretation)
  (v : State)
  {n : ℕ}
  {args : TermVector n}
  : Subst.adjoint (TermVector.toSubst args) i v
  = (i.assignDots fun x ↦ Term.denote i v args.toVector[x]) := by
    funext s
    match s with
      | .Function (.dot m) =>
        by_cases m < n
        .
          have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
               = args.toVector[m] := by
                apply term_vector_to_subst_get.dot.mem args 0 m (by omega) (by omega)

          apply Subtype.ext
          funext args'
          simp_all[Interpretation.assignDots, FunctionSymbol.arity, Subst.adjoint]
        .
          have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
               = Term.dot m := by
                simp[TermVector.toSubst]
                apply term_vector_to_subst_get.dot.nomem m args (by omega)

          simp_all[Interpretation.assignDots]
          split
          . grind
          .
            apply Subtype.ext
            funext args

            have : args = fun x ↦ [][↑x] := by grind

            simp_all[Term.dot, Term.denote, FunctionSymbol.arity, Subst.adjoint]
            congr!
      | .Function (.udef f' a) =>
        simp only [
          Subst.adjoint,
          term_vector_to_subst_get.fn,
          Symbol.default
        ]

        apply Subtype.ext
        simp[Term.denote]

        have : ∀ x : Fin a, (Term.dots a).toVector[(↑x : ℕ)]
             = Term.dot ↑x := by apply Interpretation.dots_eq

        simp_all[Term.dot, Term.denote, Interpretation.assignDots, FunctionSymbol.arity]

      | .UnitFun F =>
        simp[Subst.adjoint]
        split
        next h =>
          rw[TermVector.toSubst_in] at h
          grind only
        . simp[Interpretation.assignDots]

      | .Predicate p =>
        simp[Subst.adjoint]

        simp only [term_vector_to_subst_get.pred]

        funext args
        simp_all[Formula.denote]

        have : ∀ (x : Fin p.arity), (Term.dots p.arity).toVector[(↑x : ℕ)]
             = Term.dot x := by apply Interpretation.dots_eq

        simp only [this]

        simp[Term.dot, Term.denote, Interpretation.assignDots]

      | .UnitPred P =>
        simp[Subst.adjoint]
        simp only [term_vector_to_subst_get.unitpred]
        simp[Formula.denote, Interpretation.assignDots]
        funext s'
        simp[setOf]
        suffices (fun x ↦ if ↑x ∈ P.taboo.toFinset then 0 else s' x) = s' by
          rw[this]
        funext x
        grind only [= Set.mem_compl_iff, = Finset.mem_coe]
      | .Program a =>
        simp[Subst.adjoint]
        simp only [term_vector_to_subst_get.program]
        simp[Program.denote, Interpretation.assignDots]

section depEqAux
open scoped ContDiff
-- Because it is dependent, Lean struggles to instantiate this congruence in a complex proof
lemma depEqAux (S : Finset Variable)
               (v : State)
               (f g : Σ x : { s : Finset Variable // Disjoint s S},
                      {g : (↑x → ℝ) → ℝ // ContDiff ℝ ∞ g})
               : f = g → (f.snd).val (fun x ↦ v ↑x) = (g.snd).val (fun x ↦ v ↑x) := by
  intro h
  rw[h]
end depEqAux

lemma Subst.adjoint_unitFun (v w : State) (i : Interpretation) (σ : Subst) (F : UnitFunctional) : Term.denote i v (σ.get (Symbol.UnitFun F)) = Term.denote (σ.adjoint i w) v (Term.unit F) := by
  simp[Term.denote]
  simp[Subst.adjoint]
  let := σ.mem_dec (Symbol.UnitFun F)
  cases this
  next h =>
    have := Subst.notin_default _ _ h
    simp[this, Term.denote, Symbol.default]
    apply depEqAux
    symm
    exact if_neg h
  next h =>
    symm
    trans
    . apply depEqAux _ _ _ _ (if_pos h)
    . simp only
      apply Term.coincidence'
      simp only [Interpretation.eq_on_rfl, and_true]
      simp_all only [Set.EqOn, SetLike.mem_coe, State.finUpdate, ↓reduceDIte, implies_true]

section applySubstFreeVarSem
-- Since the interpretation matters for `freeVarsSem` we have to add an `adjoint` when computing `t.freeVarsSem` similar to `Subst.preserve_semantics.term`.
mutual

theorem TermVector.freeVarsSem_applySubst_subset {n : ℕ} (σ : Subst) (i : Interpretation) (U : FCSet Variable) (ts as : TermVector n) (w : State)
  : TermVector.applySubst σ U ts = some as
  → ↑(as.freeVarsSem i) ⊆ ↑(ts.freeVarsSem (σ.adjoint i w)) ∪ (↑(σ.freeVarsSem i (some ts.signature)) \ U.toSet) := by
  intro h₁
  match n with
  | 0 =>
    simp only [TermVector.zero_size_eq_nil, TermVector.freeVarsSem, Finset.coe_empty,
      TermVector.signature_nil, Set.empty_union, Set.empty_subset]
  | n+1 =>
    match ts with
    | .cons t ts' =>
      simp[TermVector.applySubst, Option.bind] at h₁
      split at h₁
      . contradiction
      simp only at h₁
      split at h₁
      . contradiction
      simp at h₁
      next a heqa _ _ as' heqas' =>
      rw[←h₁]
      clear h₁
      simp only [TermVector.freeVarsSem, Finset.coe_union, TermVector.signature_cons]
      have := @σ.freeVarsSem_symbol_union i t.signature ts'.signature
      have := Term.freeVarsSem_applySubst_subset σ i U t a w heqa
      have := TermVector.freeVarsSem_applySubst_subset σ i U ts' as' w heqas'
      grind only [= Set.subset_def, = Set.mem_union, = Set.mem_diff, = Finset.mem_coe,
        = Finset.mem_union]
termination_by (σ.size, sizeOf ts)
decreasing_by
all_goals simp_wf
all_goals grind only [= Prod.lex_def]


theorem Term.freeVarsSem_applySubst_subset (σ : Subst) (i : Interpretation) (U : FCSet Variable) (t a : Term) (w : State)
  : Term.applySubst σ U t = some a
  → ↑(a.freeVarsSem i) ⊆ ↑(t.freeVarsSem (σ.adjoint i w)) ∪ (↑(σ.freeVarsSem i (some t.signature)) \ U.toSet) := by
  intro h₁
  match t with
  | .var v =>
    simp[Term.applySubst] at h₁
    simp[←h₁,Term.freeVarsSem]
  | .neg t =>
    simp_all[Term.applySubst, Option.bind]
    split at h₁
    . contradiction
    next a' heq =>
    have := Term.freeVarsSem_applySubst_subset σ i U t a' w heq
    simp_all
    rw[← h₁]
    simp only[Term.freeVarsSem, Term.signature]
    assumption
  | .plus t₁ t₂
  | .times t₁ t₂ =>
    simp[Term.applySubst, Option.bind] at h₁
    split at h₁
    . contradiction
    simp_all only
    split at h₁
    . contradiction
    next b heqb _ _ c heqc =>
    simp_all only [Term.signature]
    have := Term.freeVarsSem_applySubst_subset σ i U t₁ b w heqb
    have := Term.freeVarsSem_applySubst_subset σ i U t₂ c w heqc
    simp[Term.freeVarsSem]
    all_goals
    simp at h₁
    rw[← h₁]
    simp[Term.freeVarsSem]
    have := @Subst.freeVarsSem_symbol_union σ i t₁.signature t₂.signature
    grind only [= Set.subset_def, = Set.mem_union, = Set.mem_diff, = Finset.mem_coe,
      = Finset.mem_union]
  | .unit F =>
    simp[Term.applySubst] at h₁
    rw[←h₁]
    simp[Term.freeVarsSem, Term.signature, Subst.adjoint]
    apply Set.subset_union_of_subset_left
    split
    . rfl
    next h =>
      rw[σ.notin_default _ h]
      rfl
  | .applyFn f args =>
    match f with
    | .num n =>
      simp[Term.applySubst] at h₁
      simp[←h₁, Term.freeVarsSem, TermVector.freeVarsSem]
    | .sym s =>
      simp_all only [Term.freeVarsSem, Term.signature]
      simp[Term.applySubst, Option.bind] at h₁
      split at h₁
      . contradiction
      next a' _ =>
        split at h₁
        .
          simp at h₁
          split at h₁
          . contradiction
          next _ heq =>
            simp at h₁ heq
            rw[←Term.free_vars_decidable] at heq
            have := Term.freeVarsSem_applySubst_subset a'.toSubst i ∅ (σ.get (Symbol.Function s)) a w h₁
            rw[subst_adjoint_of_term_vector_to_subst, Term.assignDots_freeVarsSem] at this
            grw[this]
            clear this
            have := @Subst.freeVarsSem_symbol_union σ i (Function.signature (Fn.sym s)) args.signature
            grw[←this]
            clear this
            simp only [FCSet.to_set_empty, Set.diff_empty]
            have := toSubst.freeVarsSem_inc a' i (some (Term.signature (σ.get (Symbol.Function s))))
            grw[this]
            clear this
            simp only [Finset.coe_union]
            have := @Subst.free_vars_sem_subset_fun σ s i
            grw[←this]
            clear this
            have := Term.freeVarsSem_subset_freeVars
            have := TermVector.freeVarsSem_applySubst_subset σ i U args a' w (by assumption)
            grw[this]
            clear this
            simp_all only [← Set.disjoint_iff_inter_eq_empty, Set.union_subset_iff,
              Set.subset_union_left, true_and]
            grind only [= Set.disjoint_left, = Set.subset_def, = Set.mem_union, = Set.mem_diff]
        .
          simp at h₁
          rw[← h₁]
          simp[Term.freeVarsSem]
          have := TermVector.freeVarsSem_applySubst_subset σ i U args a' (by assumption)
          have := @Subst.freeVarsSem_symbol_union σ
          grind only [= Set.subset_def, = Set.mem_union, = Set.mem_diff, = Finset.mem_coe,
            = Finset.mem_union]
  | .differential t =>
    simp[Term.applySubst, Option.bind] at h₁
    split at h₁
    . contradiction
    simp at h₁
    next a' heq =>
      rw[←h₁]
      clear h₁
      have := Term.freeVarsSem_applySubst_subset σ i .univ _ _ w heq
      simp only [Term.freeVarsSem, Finset.coe_union, Finset.coe_map, Term.signature, FCSet.to_set_univ, Set.diff_univ, Set.union_empty] at *
      grind only [= Set.mem_diff, = Set.mem_image, = Set.mem_union, = Set.subset_def]

termination_by (σ.size, sizeOf t)
decreasing_by
all_goals simp_wf
all_goals (try grind only [= Prod.lex_def])
next hin _ _ _ _ _ =>
  rw[TermVector.toSubst_size]
  apply Subst.symbol_size at hin
  grind only [= Prod.lex_def]
end

theorem Term.freeVarsSem_applySubst_univ_subset (σ : Subst) (i : Interpretation) (w : State) (t a : Term)
  : Term.applySubst σ FCSet.univ t = some a
  → a.freeVarsSem i ⊆ t.freeVarsSem (σ.adjoint i w) := by
  intros h _
  have := Term.freeVarsSem_applySubst_subset σ i FCSet.univ t a w h
  simp only [FCSet.to_set_univ, Set.diff_univ, Set.union_empty,
    SetLike.coe_subset_coe, Finset.le_eq_subset] at this
  apply this

end applySubstFreeVarSem


theorem Subst.preserve_semantics.term
  (σ : Subst)
  (U : FCSet Variable)
  (i : Interpretation)
  (v w : State)
  (hvw : v.isEqExcept w U)
  (t t' : Term)
  (hs : t' = Term.applySubst σ U t)
  : Term.denote i v t' = Term.denote (Subst.adjoint σ i w) v t := by
  match t with
    | .var x => simp_all[Term.applySubst, Term.denote]
    | .neg t =>
      simp[Term.applySubst, Option.bind] at hs
      split at hs
      . contradiction
      .
        next a heq =>
        have := Subst.preserve_semantics.term σ U i v w hvw t a (by simp[heq])
        simp_all[Term.denote]
    | .plus t₁ t₂
    | .times t₁ t₂ =>
      simp[Term.applySubst, Option.bind] at hs
      split at hs
      . contradiction
      .
        simp at hs
        split at hs
        . contradiction
        .
          next a ha _ _ b hb =>
          have := Subst.preserve_semantics.term σ U i v w hvw t₁ a (by simp[ha])
          have := Subst.preserve_semantics.term σ U i v w hvw t₂ b (by simp[hb])
          simp_all[Term.denote]
    | .unit F =>
      simp[Term.applySubst] at hs
      rw[hs]
      rw[Subst.adjoint_unitFun _ w]
    | .applyFn f args =>
      match hf : f with
        | .num n =>
          simp[Term.applySubst] at hs
          simp_all[Term.denote]
        | .sym s =>
          simp[Term.applySubst, Option.bind] at hs
          split at hs
          .
            contradiction
          .
            simp at hs
            -- we do apply the subst
            split at hs
            next _ b _ _ =>
              split at hs
              . contradiction
              simp_all
              simp[Term.denote]

              -- remove adjoint by Subst.preserve_semantics.termVector
              have : (fun (x : Fin s.arity) =>
                        Term.denote (σ.adjoint i w) v args.toVector[↑(x : Nat)])
                   = (fun (x : Fin s.arity) => Term.denote i v b.toVector[↑x]) := by
                    funext x
                    apply Eq.symm
                    apply Subst.preserve_semantics.term _ _ _ _ _ hvw
                    apply Eq.symm
                    apply Subst.apply_subst_term_vector_to_term
                    assumption
              rw[this]

              apply Subst.preserve_semantics.term b.toSubst _ _ v v at hs
              .
                rw[hs]
                rw[subst_adjoint_of_term_vector_to_subst]
                simp only [adjoint]
                apply Term.coincidence
                simp_all[State.isEqExcept, Term.free_vars_decidable, ←Set.disjoint_iff_inter_eq_empty]
                grind only [= Set.disjoint_left, Set.EqOn, = Set.mem_compl_iff]
              .
                simp_all only [State.isEqExcept, FCSet.to_set_empty, Set.compl_empty, Set.eqOn_univ]
            next a _ _ =>
              -- we don't apply subst
              simp_all

              -- remove adjoint by Subst.preserve_semantics.termVector
              have : (fun (x : Fin s.arity) =>
                        Term.denote (σ.adjoint i w) v args.toVector[↑(x : ℕ)])
                   = (fun (x : Fin s.arity) => Term.denote i v a.toVector[↑x]) := by
                    funext x
                    apply Eq.symm
                    apply Subst.preserve_semantics.term _ _ _ _ _ hvw
                    apply Eq.symm
                    apply Subst.apply_subst_term_vector_to_term
                    assumption

              simp[Term.denote]
              rw[this]

              -- remove remaining adjoint because `σ.adjoint i w f = i f` if `f ∉ σ`
              have := @Subst.adjoint_noeffect_nomem i w s σ (by assumption)
              rw[this]
              simp

    | .differential t =>
      simp[Term.applySubst, Option.bind] at hs
      split at hs
      . contradiction
      next a heq =>
      simp at hs
      cases hs
      simp[Term.denote]

      have : ∀ x ∈ (t.freeVarsSem (σ.adjoint i w) \ a.freeVarsSem i),
        (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x) = 0 := by
        intro x hx
        apply mul_eq_zero_of_right

        have : ∀ (y : ℝ), Term.denote i (v.update x y) a
                        = Term.denote i v a := by
          intro y
          apply Term.coincidence' a i i (v.update x y) v
          and_intros
          .
            intro z
            simp[State.update, Function.update]
            grind
          . simp
        simp only [this]
        apply deriv_const

      -- because the taboo is `FCSet.univ`
      -- the substitution can *only reduce* free variables, e.g. {f(⋅) → 2}
      have : a.freeVarsSem i ⊆ t.freeVarsSem (σ.adjoint i w) := by
        apply Term.freeVarsSem_applySubst_univ_subset
        assumption

      have : ∑ x ∈ a.freeVarsSem i, (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x)
           = ∑ x ∈ t.freeVarsSem (σ.adjoint i w), (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x)
           := by
           apply Finset.sum_subset
           . assumption
           . grind
      rw[this]

      congr 1
      funext x
      congr
      funext y
      apply Subst.preserve_semantics.term _ FCSet.univ
      . simp only [FCSet.to_set_univ, State.eq_except_univ]
      . simp_all only

termination_by
  (σ.size, sizeOf t)
decreasing_by
  all_goals simp[Prod.lex_def]
  . omega
  . omega
  .
    have ha : sizeOf args.toVector[↑x] < sizeOf args := by
      apply TermVector.sizeOf_lt_of_mem
      simp[TermVector.mem_toVector_iff]
    grind
  .
    have ha : sizeOf args.toVector[↑x] < sizeOf args := by
      apply TermVector.sizeOf_lt_of_mem
      simp[TermVector.mem_toVector_iff]
    grind
  .
    have := Subst.symbol_size σ s (by assumption)
    have := @TermVector.toSubst_size s.arity
    grind

set_option maxHeartbeats 0 in
/- Good things take time (dunno if that is one of them) --/

mutual

theorem Subst.preserve_semantics.formula
  (σ : Subst)
  (U : FCSet Variable)
  (i : Interpretation)
  (v w : State)
  (hvw : v.isEqExcept w U)
  (Φ Φ' : Formula)
  (hs : Φ' = Formula.applySubst σ U Φ)
  : v ∈ Formula.denote i Φ' ↔ v ∈ Formula.denote (Subst.adjoint σ i w) Φ := by
    match Φ with
      | .True
      | .False =>
        simp_all[Formula.denote, Formula.applySubst]
      | .eq t₁ t₂
      | .gte t₁ t₂ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all[Formula.denote]
        have := Subst.preserve_semantics.term σ U i v w hvw t₁
        have := Subst.preserve_semantics.term σ U i v w hvw t₂
        grind
      | .not Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        rename Formula => Φ'
        have := Subst.preserve_semantics.formula σ U i v w hvw Φ Φ'
        simp_all[Formula.denote]
      | .and Φ₁ Φ₂ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        next Φ₁' _ _ _ Φ₂' _ =>
        have := Subst.preserve_semantics.formula σ U i v w hvw Φ₁ Φ₁'
        have := Subst.preserve_semantics.formula σ U i v w hvw Φ₂ Φ₂'
        simp_all[Formula.denote]
      | .forall x Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        .
          intros h r
          have hvw' : (v.update x r).isEqExcept w ({x} ∪ U).toSet := by grind[Set.EqOn, State.isEqExcept]
          apply (Subst.preserve_semantics.formula σ ({x} ∪ U) i (v.update x r) w hvw' Φ Φ' (by grind)).mp (h r)

        .
          intros h r
          have hvw' : (v.update x r).isEqExcept w ({x} ∪ U).toSet := by grind[Set.EqOn, State.isEqExcept]
          apply (Subst.preserve_semantics.formula σ ({x} ∪ U) i (v.update x r) w hvw' Φ Φ' (by grind)).mpr (h r)
      | .exists x Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        .
          intro ⟨r, hr⟩
          apply Exists.intro r

          have hvw' : (v.update x r).isEqExcept w ({x} ∪ U).toSet := by grind[Set.EqOn, State.isEqExcept]
          apply (Subst.preserve_semantics.formula σ ({x} ∪ U) i (v.update x r) w hvw' Φ Φ' (by grind)).mp hr
        .
          intro ⟨r, hr⟩
          apply Exists.intro r

          have hvw' : (v.update x r).isEqExcept w ({x} ∪ U).toSet := by grind[Set.EqOn, State.isEqExcept]
          apply (Subst.preserve_semantics.formula σ ({x} ∪ U) i (v.update x r) w hvw' Φ Φ' (by grind)).mpr hr
      | .box α Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        rename FCSet Variable × Program => Vα'
        rcases Vα' with ⟨V,α'⟩
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        all_goals
        intros h₁ w' h₂
        have := Subst.preserve_semantics.program σ U V i v w w' hvw α α'
        simp_all only [iff_true, forall_const]
        have hww' : w'.isEqExcept w V.toSet := by
          have := Program.bound_effect this
          have := Program.boundVars_applySubst_subset σ U V α α'
          grind only [= Set.subset_def, State.isEqExcept, Set.EqOn, = Set.mem_compl_iff,
            = Set.mem_union]
        have := Subst.preserve_semantics.formula σ V i w' w hww' Φ Φ'
        grind only
      | .diamond α Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        rename FCSet Variable × Program => Vα'
        rcases Vα' with ⟨V,α'⟩
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        all_goals
        intro ⟨w', hw⟩
        apply Exists.intro w'
        have := Subst.preserve_semantics.program σ U V i v w w' hvw α α'
        simp_all only [iff_true, forall_const, and_true]
        have hww' : w'.isEqExcept w V.toSet := by
          have := Program.bound_effect this
          have := Program.boundVars_applySubst_subset σ U V α α'
          grind only [= Set.subset_def, State.isEqExcept, Set.EqOn, = Set.mem_compl_iff,
            = Set.mem_union]
        have := Subst.preserve_semantics.formula σ V i w' w hww' Φ Φ'
        grind only
      | .ref α β =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all[Formula.denote]
        next _ _ Vα' _ _ _ Wβ' _ =>
        apply Iff.intro
        all_goals
        intros h₁ w' h₂
        have := Subst.preserve_semantics.program σ U Vα'.1 i v w w' hvw α Vα'.2
        have := Subst.preserve_semantics.program σ U Wβ'.1 i v w w' hvw β Wβ'.2
        grind
      | .unit P =>
        simp[Formula.applySubst] at hs
        simp[hs, Formula.denote, Subst.adjoint]
        change _ ↔ (fun x ↦ if x ∈ P.taboo.toFinset then 0 else v x) ∈ Formula.denote i (σ.get (Symbol.UnitPred P))
        apply Iff.intro
        all_goals
        apply Formula.coincidence
        have := Subst.get_unitPred_freeVars σ P
        simp_all[Set.EqOn]
        grind only [= Set.disjoint_left, usr Set.mem_setOf_eq]
      | .applyPred p args =>
        simp[Formula.applySubst, Option.bind] at hs
        split at hs
        . contradiction
        simp only at hs

        next _ args' _ =>
        have : (fun (x : Fin p.arity) => Term.denote (σ.adjoint i w) v args.toVector[↑(x : ℕ)])
             = (fun (x : Fin p.arity) => Term.denote i v args'.toVector[↑x]) := by
                  funext x
                  apply Eq.symm
                  apply Subst.preserve_semantics.term _ U _ _ _ hvw
                  apply Eq.symm
                  apply Subst.apply_subst_term_vector_to_term
                  assumption

        split at hs
        . split at hs
          . contradiction
          simp_all
          -- we do apply the subst
          apply Subst.preserve_semantics.formula args'.toSubst ∅ i v v at hs
          .
            rw[hs]
            rw[subst_adjoint_of_term_vector_to_subst]
            simp[Formula.denote, adjoint]
            rw[this]
            apply Iff.intro
            all_goals
            apply Formula.coincidence
            simp_all[State.isEqExcept, ←Set.disjoint_iff_inter_eq_empty]
            grind only [Formula.free_vars_decidable, = Set.disjoint_left, Set.EqOn, = Set.mem_compl_iff]
          .
            simp_all only [State.isEqExcept, FCSet.to_set_empty, Set.compl_empty, Set.eqOn_univ]
        .
          -- we dont apply the subst
          have := @Subst.adjoint_noeffect_nomem i w p σ (by assumption)
          simp_all[Formula.denote, Subst.adjoint]
termination_by (σ.size, Φ.size)
decreasing_by
  all_goals simp[Prod.lex_def, Formula.size]
  . omega
  . omega
  . omega
  . omega
  . omega
  . omega
  . omega
  .
    have := Subst.symbol_size σ p (by assumption)
    have := @TermVector.toSubst_size p.arity
    grind

theorem Subst.preserve_semantics.program
  (σ : Subst)
  (U V : FCSet Variable)
  (i : Interpretation)
  (v v' w : State)
  (hvv' : v.isEqExcept v' U)
  (α α' : Program)
  (hs : some ⟨V,α'⟩ = Program.applySubst σ U α)
  : ⟨v, w⟩ ∈ Program.denote i α' ↔ ⟨v, w⟩ ∈ Program.denote (Subst.adjoint σ i v') α := by
    match α with
      | .const a =>
        simp_all[Program.denote, Program.applySubst, Subst.adjoint]
      | .assign x t =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        rename Term => t'
        simp_all[Program.denote]
        have := Subst.preserve_semantics.term σ U i v _ hvv' t t'
        grind
      | .random x =>
        simp[Program.applySubst] at hs
        rw[hs.2]
        simp only [Program.denote]
      | .test Φ =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        rename Formula => Φ'
        simp_all[Program.denote]
        have := Subst.preserve_semantics.formula σ U i v _ hvv' Φ Φ'
        grind
      | .choice α β =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all[Program.denote]
        next _ _ _ Vα' _ _ _ Wβ' _ =>
        have := Subst.preserve_semantics.program σ U Vα'.1 i v _ w hvv' α Vα'.2
        have := Subst.preserve_semantics.program σ U Wβ'.1 i v _ w hvv' β Wβ'.2
        grind
      | .seq α β =>
        simp[Program.applySubst, Option.bind] at hs
        split at hs
        . contradiction
        simp only at hs
        split at hs
        . contradiction
        simp_all[Program.denote]
        next Vα' _ _ _ Wβ' _  =>
        rcases Vα' with ⟨V,α'⟩
        rcases Wβ' with ⟨W,β'⟩
        apply Iff.intro
        all_goals
          intro ⟨w', hw'⟩
          apply Exists.intro w'
          have := Subst.preserve_semantics.program σ U V i v _ w' hvv' α α'
          simp_all only [iff_true, forall_const, true_and]
          have hw'v' : w'.isEqExcept v' V.toSet := by
            have := Program.bound_effect this
            have := Program.boundVars_applySubst_subset σ U V α α'
            grind only [= Set.subset_def, State.isEqExcept, Set.EqOn, = Set.mem_compl_iff,
              = Set.mem_union]
          have := Subst.preserve_semantics.program σ V W i w' _ w hw'v' β β'
          grind only
      | .loop α =>
        simp[Program.applySubst, Option.bind] at hs
        split at hs
        . contradiction
        -- first pass to get bound variables
        simp at hs
        rename FCSet Variable × Program => Vα'
        rcases Vα' with ⟨V, α'⟩
        set V' := Program.substBoundVars σ α ∪ U
        have := Subst.preserve_semantics.program σ U V i v _ w hvv' α α'

        simp_all[Program.denote]
        apply Iff.intro
        all_goals
          intros h
          induction h with
            | rfl => grind[LoopClosure]
            | trans v₂ w h₁ h₂ ih =>
                have := ih (by apply Subst.preserve_semantics.program _ _ _ _ _ _ _ hvv')
                apply LoopClosure.trans (v := v₂)
                . grind only
                .
                  have hv₂v' : v₂.isEqExcept v' V'.toSet := by
                    have := @Program.bound_effect α'.loop v v₂ i
                    simp_all only [Program.denote, Set.mem_setOf_eq, Program.boundVars,
                      forall_const]
                    have := Program.boundVars_applySubst_subset σ V' V α α'
                    have := @Program.substBoundVars_applySubst σ α α' V' V
                    grind[!FCSet.to_set_union, State.isEqExcept, Set.EqOn]
                  have := Subst.preserve_semantics.program σ V' V i v₂ v' w hv₂v' α α'
                  simp_all[Membership.mem, Set.Mem]
      | .ode system Ψ =>
        simp[Program.applySubst, Option.bind] at hs
        split at hs
        . contradiction
        simp only at hs
        split at hs
        . contradiction
        simp_all[Program.denote, -FCSet.to_set_eq]
        rename List ODE => ssystem
        rename Formula => Ψ'
        set V' := FCSet.Finite (system.variables ∪ Finset.map Variable.diff_emb system.variables) ∪ U

        have hassign : OdeSystem.variables ssystem = OdeSystem.variables system :=
          ode_mapM_variables_eq (show _ = some ssystem from ‹_›)

        rw[hassign]
        apply Iff.intro
        all_goals
          rintro ⟨r, hr, φ, heq0, heqr, hflow⟩
          apply Exists.intro r
          and_intros
          . grind
          .
            apply Exists.intro φ
            and_intros
            . grind
            . grind
            .
              intros ζ  h₁ h₂
              and_intros
              .
                have := hflow ζ h₁ h₂

                have := ode_evolution_formula_applySubst
                          (σ := σ) (U := V') (system := system) (ssystem := ssystem)
                          (Ψ := Ψ) (Ψ' := Ψ') (by grind) (by grind)

                have hφv' : (φ ζ).isEqExcept v' V'.toSet := by
                  specialize hflow ζ h₁ h₂
                  clear * - hvv' heq0 hflow
                  grind[State.isEqExcept, Set.EqOn, OdeSystem.variables]
                have := Subst.preserve_semantics.formula σ V' i (φ ζ) v' hφv'
                          (odeEvolutionFormula system Ψ)
                          (odeEvolutionFormula ssystem Ψ') (by grind)
                grind only
              . grind
              . grind
termination_by (σ.size, α.size)
decreasing_by
  all_goals simp[Prod.lex_def, Program.size]
  all_goals grind[ode_evolution_formula_size_bound]

end

-- Uniform Substitution for Differential Dynamic Logic is sound!
theorem US {σ : Subst} {Φ Φ' : Formula}
  : Formula.applySubst σ ∅ Φ = Φ'
  → (∀ (i : Interpretation) (v : State), v ∈ Formula.denote i Φ)
  → (∀ (i : Interpretation) (v : State), v ∈ Formula.denote i Φ') := by
  intros h₁ h₂ i v
  have := h₂ i v
  have := Subst.preserve_semantics.formula σ ∅ i v v (Set.eqOn_refl _ _) Φ Φ' (by grind)
  simp_all

theorem US_rule {σ : Subst}
                (premises : List (Formula × Formula))
                (Ψ Ψ' : Formula)
                (hp : ∀ Φ ∈ premises, Formula.applySubst σ .univ Φ.1 = Φ.2)
                (hΨ : Formula.applySubst σ .univ Ψ = Ψ')
  : (∀ (i : Interpretation), (∀ (v : State) (Φ : Formula × Formula), Φ ∈ premises → v ∈ Formula.denote i Φ.1) → (∀ (v : State), v ∈ Formula.denote i Ψ))
  → (∀ (i : Interpretation), (∀ (v : State) (Φ : Formula × Formula), Φ ∈ premises → v ∈ Formula.denote i Φ.2) → (∀ (v : State), v ∈ Formula.denote i Ψ')) := by
  intros h₁ i h₂ v

  have : ∀ (w : State), ∀ Φ ∈ premises, w ∈ Formula.denote (σ.adjoint i v) Φ.1:= by
    intros w Φ hp
    have := Subst.preserve_semantics.formula σ .univ i w v (by grind[State.isEqExcept, Set.EqOn]) Φ.1 Φ.2 (by grind only)
    grind only

  have : v ∈ Formula.denote (σ.adjoint i v) Ψ :=
    h₁ (Subst.adjoint σ i v) this v

  have := Subst.preserve_semantics.formula σ .univ i v v (Set.eqOn_refl _ _) Ψ Ψ' (by grind)
  grind only
