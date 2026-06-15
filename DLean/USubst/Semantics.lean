import DLean.USubst.Subst
import DLean.Semantics.State
import DLean.Semantics.Interpretation

open Semantics

-- Unused
theorem Subst.adjoint_term_noeffect.pred
  (i : Interpretation)
  (p : PredicateSymbol)
  {rhs : Formula}
  {es : List SubstEntry}
  (hsubst : Subst.Nodup (SubstEntry.pred p rhs :: es))
  (t : Term)
  (v w : State)
  : Term.denote (Subst.adjoint ⟨SubstEntry.pred p rhs :: es, hsubst⟩ i v) w t
  = Term.denote (Subst.adjoint ⟨es, Subst.tail_nodup hsubst⟩ i v) w t := by
  match t with
    | .var x => simp[Term.denote]
    | .neg t' =>
      have := @Subst.adjoint_term_noeffect.pred i p rhs es hsubst t'
      simp_all only [Term.denote]
    | .plus t₁ t₂
    | .times t₁ t₂ =>
      have := @Subst.adjoint_term_noeffect.pred i p rhs es hsubst t₁
      have := @Subst.adjoint_term_noeffect.pred i p rhs es hsubst t₂
      simp_all only [Term.denote]
    | .applyFn f args =>
      match f with
        | .num n => simp[Term.denote]
        | .sym f =>
          match f with
            | .dot n =>
              have := @Subst.get_tail
                        ⟨es, Subst.tail_nodup hsubst⟩
                        (.Function (.dot n))
                        (.pred p rhs)
                        (by simp_all)
                        (by simp[SubstEntry.symbol])
              simp_all[Term.denote, Subst.adjoint, FunctionSymbol.arity]
            | .udef name arity =>
              simp[Term.denote, Subst.adjoint]
              congr 1
              .
                congr
                funext x
                apply Subst.adjoint_term_noeffect.pred i
              .
                have := @Subst.get_tail
                          ⟨es, Subst.tail_nodup hsubst⟩
                          (.Function (.udef name arity))
                          (.pred p rhs)
                          (by simp_all)
                          (by simp[SubstEntry.symbol])

                rw[this]
    | .differential t =>
      simp[Term.denote]
      apply Finset.sum_equiv (by rfl) (fun i ↦ by rfl)
      intros
      congr
      funext
      apply Subst.adjoint_term_noeffect.pred i
decreasing_by
  all_goals try decreasing_trivial
    -- TODO automate this?
  have ha : sizeOf args.toVector[x] < sizeOf args := by
    apply TermVector.sizeOf_lt_of_mem
    simp[TermVector.mem_toVector_iff]

  have hb : sizeOf args
          < sizeOf (Term.applyFn (.sym (FunctionSymbol.udef name arity)) args) := by simp
  grind

theorem Subst.adjoint_noeffect_nomem_fun
  (i : Interpretation)
  (v : State)
  (f : FunctionSymbol)
  {σ : Subst}
  : (.Function f) ∉ σ
  → (σ.adjoint i v (Symbol.Function f)) = i f := by
    intro h
    match hs : σ with
      | ⟨.nil, _⟩ =>
        simp_all[Subst.adjoint, Subst.get, Symbol.default, Term.denote]
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
      | ⟨x::xs, h⟩ =>
        have := by
          apply @Subst.adjoint_noeffect_nomem_fun i v f ⟨xs, Subst.tail_nodup h⟩
          simp_all[Membership.mem, Subst.mem]
        simp_all[Subst.adjoint, Subst.get]
        split
        . simp_all[Membership.mem, Subst.mem]
        . simp_all
termination_by
  σ.1

theorem Subst.adjoint_noeffect_nomem_pred
  (i : Interpretation)
  (v : State)
  (p : PredicateSymbol)
  {σ : Subst}
  : (.Predicate p) ∉ σ
  → (σ.adjoint i v (Symbol.Predicate p)) = i p := by
    intro h
    match hs : σ with
      | ⟨.nil, _⟩ =>
        simp_all[Subst.adjoint, Subst.get, Symbol.default, Formula.denote]

        have : ∀ (x : Fin p.arity), (Term.dots p.arity).toVector[(↑x : ℕ)]
             = Term.dot x := by
                apply Interpretation.dots_eq

        simp_all[Term.dot, Term.denote, Interpretation.assignDots]
      | ⟨x::xs, h⟩ =>
        have := by
          apply @Subst.adjoint_noeffect_nomem_pred i v p ⟨xs, Subst.tail_nodup h⟩
          simp_all[Membership.mem, Subst.mem]
        simp_all[Subst.adjoint, Subst.get]
        split
        . simp_all[Membership.mem, Subst.mem]
        . simp_all
termination_by
  σ.1

theorem term_vector_to_subst_get.fn
  {n : ℕ}
  {args : TermVector n}
  {k : ℕ}
  {f : String}
  {a : ℕ}
  (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (Symbol.Function (FunctionSymbol.udef f a))
  = Symbol.default (FunctionSymbol.udef f a) := by
  cases args with
      | nil =>
        simp_all [TermVector.toSubstAux, Symbol.default, Subst.get]
      | cons _ as =>
        simp_all [TermVector.toSubstAux, Subst.get]
        split
        .
          next h =>
          cases h
        .
          have := @term_vector_to_subst_get.fn _ as (k + 1) f a
          simp_all

theorem term_vector_to_subst_get.pred
  {n : ℕ}
  {args : TermVector n}
  {k : ℕ}
  {p : PredicateSymbol}
  (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (.Predicate p)
  = Formula.applyPred p (Term.dots p.arity) := by
    cases args with
      | nil =>
        simp_all [TermVector.toSubstAux, Symbol.default, Subst.get]
      | cons _ as =>
        simp_all [TermVector.toSubstAux, Subst.get]
        split
        . contradiction
        .
          have := @term_vector_to_subst_get.pred _ as (k + 1) p
          simp_all

theorem term_vector_to_subst_get.program
  {n : ℕ}
  {args : TermVector n}
  {k : ℕ}
  {a : ProgramSymbol}
  (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (.Program a)
  = Program.const a := by
    cases args with
      | nil =>
        simp_all [TermVector.toSubstAux, Symbol.default, Subst.get]
      | cons _ as =>
        simp_all [TermVector.toSubstAux, Subst.get]
        split
        . contradiction
        .
          have := @term_vector_to_subst_get.program _ as (k + 1) a
          simp_all


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
  (k : ℕ)
  (h : m ≥ n + k)
  (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (Symbol.Function (FunctionSymbol.dot m))
  = Term.dot m := by
  cases args with
    | nil =>
      simp_all [TermVector.toSubstAux, Subst.get, Symbol.default, Term.dot]
    | cons a as =>
      simp_all [TermVector.toSubstAux, Subst.get]
      split
      .
        next _ h =>
        cases h
        grind
      .
        apply term_vector_to_subst_get.dot.nomem m as (k + 1) (by omega)

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
                apply term_vector_to_subst_get.dot.nomem m args 0 (by omega)

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
          TermVector.toSubst,
          term_vector_to_subst_get.fn,
          Symbol.default
        ]

        apply Subtype.ext
        simp[Term.denote]

        have : ∀ x : Fin a, (Term.dots a).toVector[(↑x : ℕ)]
             = Term.dot ↑x := by apply Interpretation.dots_eq

        simp_all[Term.dot, Term.denote, Interpretation.assignDots, FunctionSymbol.arity]

      | .Predicate p =>
        simp[Subst.adjoint]

        simp only [TermVector.toSubst, term_vector_to_subst_get.pred]

        funext args
        simp_all[Formula.denote]

        have : ∀ (x : Fin p.arity), (Term.dots p.arity).toVector[(↑x : ℕ)]
             = Term.dot x := by apply Interpretation.dots_eq

        simp only [this]

        simp[Term.dot, Term.denote, Interpretation.assignDots]
      | .Program a =>
        simp[Subst.adjoint]
        simp only [TermVector.toSubst, term_vector_to_subst_get.program]
        simp[Program.denote, Interpretation.assignDots]

theorem Subst.apply_subst_term_vector_to_term
  (σ : Subst)
  (U : FCSet Assignable)
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


lemma toSubstAux.freeVars_inc {n : ℕ} (args : TermVector n) (S : Option (Finset Symbol)) :
  ∀ k, (Subst.freeVars ⟨args.toSubstAux k, (args.toSubstLemma k).1⟩ S).toSet ⊆ args.freeVars := by
  match args with
    | .nil =>
      simp[TermVector.toSubstAux, Subst.freeVars]
    | .cons e args' =>
      simp[TermVector.toSubstAux]
      unfold Subst.freeVars
      simp only
      intro k
      have := toSubstAux.freeVars_inc args' S (k+1)
      simp only [SubstEntry.freeVars]
      split
      . simp only [FCSet.to_set_union, Set.to_set_finite]
        exact Set.union_subset_union_right _ this
      . split
        . simp only [FCSet.to_set_union, Set.to_set_finite]
          exact Set.union_subset_union_right _ this
        . exact Set.subset_union_of_subset_right this _

theorem toSubst.freeVars_inc {n : ℕ} (args : TermVector n) (S : Option (Finset Symbol)) :
  (args.toSubst.freeVars S).toSet ⊆ args.freeVars := by
  exact toSubstAux.freeVars_inc _ _ 0

mutual

theorem TermVector.freeVars_applySubst_subset {n : ℕ} (σ : Subst) (U : FCSet Assignable) (ts as : TermVector n)
  : TermVector.applySubst σ U ts = some as
  → ↑as.freeVars ⊆ ↑ts.freeVars ∪ (σ.freeVars (some ts.signature) \ U).toSet := by
  intro h₁
  match n with
  | 0 =>
    simp only [TermVector.zero_size_eq_nil, TermVector.freeVars_nil, Finset.coe_empty,
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
      simp only [TermVector.freeVars_cons, Finset.coe_union, TermVector.signature_cons]
      have := @σ.freeVars_symbol_union t.signature ts'.signature
      have := Term.freeVars_applySubst_subset σ U t a heqa
      have := TermVector.freeVars_applySubst_subset σ U ts' as' heqas'
      grind only [= Set.subset_def, FCSet.to_set_diff, = Set.mem_union, = Set.mem_diff]
termination_by (σ.size, sizeOf ts)
decreasing_by
all_goals simp_wf
all_goals grind only [= Prod.lex_def]

theorem Term.freeVars_applySubst_subset (σ : Subst) (U : FCSet Assignable) (t a : Term)
  : Term.applySubst σ U t = some a
  → ↑a.freeVars ⊆ ↑t.freeVars ∪ (σ.freeVars (some t.signature) \ U).toSet := by
  intro h₁
  match t with
  | .var v => simp_all[Term.applySubst]
  | .neg t =>
    simp_all[Term.applySubst, Option.bind]
    split at h₁
    . contradiction
    next a' heq =>
    have := Term.freeVars_applySubst_subset σ U t a' heq
    simp_all
    rw[← h₁]
    simp only[Term.freeVars, Term.signature]
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
    have := Term.freeVars_applySubst_subset σ U t₁ b heqb
    have := Term.freeVars_applySubst_subset σ U t₂ c heqc
    simp[Term.freeVars]
    all_goals
    simp at h₁
    rw[← h₁]
    simp[Term.freeVars]
    have := @Subst.freeVars_symbol_union σ t₁.signature t₂.signature
    grind only [= Set.subset_def, FCSet.to_set_diff, = Set.mem_union, = Set.mem_diff]
  | .applyFn f args =>
    match f with
    | .num n =>
      simp[Term.applySubst] at h₁
      simp_all
    | .sym s =>
      simp_all only [Term.freeVars, Term.signature]
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
            have := TermVector.freeVars_applySubst_subset σ U args a' (by assumption)
            have := Term.freeVars_applySubst_subset a'.toSubst ∅ (σ.get (Symbol.Function s)) a h₁
            have := @toSubst.freeVars_inc _ a' (some (Term.signature (σ.get (Symbol.Function s))))
            have := @Subst.freeVars_symbol_union σ (Function.signature (Fn.sym s)) args.signature
            have := @Subst.free_vars_subset_fun σ s
            simp_all only [←Set.disjoint_iff_inter_eq_empty]
            grind only [= Set.disjoint_left, = Set.subset_def, FCSet.to_set_diff,
              = Set.mem_union, = Set.mem_diff]
        .
          simp at h₁
          rw[← h₁]
          simp[Term.freeVars]
          have := TermVector.freeVars_applySubst_subset σ U args a' (by assumption)
          have := @Subst.freeVars_symbol_union σ
          grind only [= Set.subset_def, FCSet.to_set_diff, = Set.mem_union, = Set.mem_diff]

  | .differential t =>
    simp[Term.applySubst, Option.bind] at h₁
    split at h₁
    . contradiction
    simp at h₁
    next a' heq =>
      rw[←h₁]
      clear h₁
      have := Term.freeVars_applySubst_subset σ .univ _ _ heq
      simp only [Term.freeVars, Finset.coe_union, Finset.coe_map, Term.signature, FCSet.to_set_diff, FCSet.to_set_univ, Set.diff_univ, Set.union_empty] at *
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

theorem Term.freeVars_applySubst_admissible_univ_subset (σ : Subst) (t a : Term)
  : Term.applySubst σ FCSet.univ t = some a
  → (a.freeVars : Set Assignable ) ⊆ (t.freeVars : Set Assignable) := by
  intros h _
  have := Term.freeVars_applySubst_subset σ FCSet.univ t a h
  simp only [FCSet.to_set_diff, FCSet.to_set_univ, Set.diff_univ, Set.union_empty,
    SetLike.coe_subset_coe, Finset.le_eq_subset] at this
  apply this

theorem Subst.preserve_semantics.term
  (σ : Subst)
  (U : FCSet Assignable)
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
                simp_all[State.isEqExcept, ←Set.disjoint_iff_inter_eq_empty]
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
              have := @Subst.adjoint_noeffect_nomem_fun i w s σ (by assumption)
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

      have : ∀ x ∈ (t.freeVars \ a.freeVars),
        (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x) = 0 := by
        intro x hx
        apply mul_eq_zero_of_right

        -- have : x ∉ a.freeVars := by grind

        have : ∀ (y : ℝ), Term.denote i (v.update x y) a
                        = Term.denote i v a := by
          intro y
          apply Term.coincidence a i i (v.update x y) v
          and_intros
          .
            intro z
            simp[State.update, Function.update]
            grind
          . simp
        simp only [this]
        apply deriv_const

      -- because hg : guard (σ.admissible FCSet.univ t.signature)
      -- and hence substitution can *only reduce* free variables, e.g. {f(⋅) → 2}
      have : a.freeVars ⊆ t.freeVars := by
        have ih := Term.freeVars_applySubst_admissible_univ_subset
              (σ := σ) t a heq
        intro x hx
        have := ih hx
        grind

      have : ∑ x ∈ a.freeVars, (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x)
           = ∑ x ∈ t.freeVars, (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x)
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


lemma ode_mapM_assignables_eq
  {σ : Subst}
  {system : OdeSystem}
  {ssystem : OdeSystem}
  (h : system.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ ∅ x.term))
       = some ssystem)
  : OdeSystem.assignables ssystem = OdeSystem.assignables system := by
  unfold OdeSystem.assignables at *;
  induction system generalizing ssystem <;> simp_all +decide [ List.mapM_cons ];
  cases h' : Term.applySubst σ ∅ ‹ODE›.term <;> simp_all +decide [ Option.bind_eq_some_iff ];
  aesop

lemma ode_evolution_formula_applySubst
  {σ : Subst}
  {system ssystem : OdeSystem}
  {Ψ Ψ' : Formula}
  : Formula.applySubst σ Ψ = some Ψ'
  → system.mapM (fun x => do return ODE.mk x.var (← Term.applySubst σ ∅ x.term)) = some ssystem
  → Formula.applySubst σ (odeEvolutionFormula system Ψ)
  = some (odeEvolutionFormula ssystem Ψ') := by

  intros h₁ h₂
  induction system generalizing ssystem Ψ Ψ' with
    | nil => simp_all[odeEvolutionFormula]
    | cons head tail ih =>
      cases _ : Term.applySubst σ ∅ head.term
      . simp_all
      .
        simp_all[Option.bind_eq_some_iff]
        simp_all[odeEvolutionFormula, Term.applySubst, Formula.applySubst]
        aesop

lemma ode_evolution_formula_admissible
  (σ : Subst)
  (system : OdeSystem)
  (Ψ : Formula)
  (U : FCSet Assignable)
  (hΨ : σ.admissible U Ψ.signature)
  (hterms : ∀ x ∈ system, σ.admissible U x.term.signature)
  : σ.admissible U (odeEvolutionFormula system Ψ).signature := by
  by_contra h;
  have h_ode : ∀ (system : OdeSystem) (Ψ : Formula), (odeEvolutionFormula system Ψ).signature = system.foldr (fun x s => x.term.signature ∪ s) Ψ.signature := by
    intros system Ψ; induction system generalizing Ψ <;> simp +decide [ * ] ;
    · rfl;
    · rename_i x xs ih; simp +decide [ *, odeEvolutionFormula ] ;
      convert congr_arg₂ ( · ∪ · ) ( show ( Formula.eq ( Term.var x.var.diff ) x.term ).signature = x.term.signature from ?_ ) ( ih Ψ ) using 1;
      exact Finset.union_eq_right.mpr ( by simp +decide [ Term.signature ] );
  refine h ?_;
  rw [h_ode];
  have h_foldr : ∀ (system : List (ODE)), (∀ x ∈ system, σ.admissible U x.term.signature) → σ.admissible U (List.foldr (fun x s => x.term.signature ∪ s) Ψ.signature system) := by
    intro system hterms; induction system <;> simp[*] ;
    rename_i k hk ih;
    have h_foldr : σ.admissible U (k.term.signature ∪ List.foldr (fun x s => x.term.signature ∪ s) Ψ.signature hk) := by
      exact Subst.admissible_symbol_union.mpr ⟨ hterms k ( by simp +decide ), ih fun x hx => hterms x ( by simp +decide [ hx ] ) ⟩;
    convert h_foldr using 1;
    unfold Subst.admissible; aesop;
  exact h_foldr system hterms

set_option maxHeartbeats 0 in
/- Good things take time (dunno if that is one of them) --/

mutual

theorem Subst.preserve_semantics.formula
  (σ : Subst)
  (i : Interpretation)
  (v : State)
  (Φ Φ' : Formula)
  (hs : Φ' = Formula.applySubst σ Φ)
  : v ∈ Formula.denote i Φ' ↔ v ∈ Formula.denote (Subst.adjoint σ i v) Φ := by
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
        have := Subst.preserve_semantics.term σ ∅ i v _ (Set.eqOn_refl _ _) t₁
        have := Subst.preserve_semantics.term σ ∅ i v _ (Set.eqOn_refl _ _) t₂
        grind
      | .not Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        rename Formula => Φ'
        have := Subst.preserve_semantics.formula σ i v Φ Φ'
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
        have := Subst.preserve_semantics.formula σ i v Φ₁ Φ₁'
        have := Subst.preserve_semantics.formula σ i v Φ₂ Φ₂'
        simp_all[Formula.denote]
      | .forall x Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        .
          intros h r
          have := (Subst.preserve_semantics.formula σ i (v.update x r) Φ Φ' (by grind)).mp (h r)
          have := Subst.admissible_adjoint.formula (U := {.var x}) (Φ := Φ) (i := i) (σ := σ)
                                                   (v := v) (w := v.update x r)
                                                   (by simp_all[Subst.admissible])
                                                   (by simp_all[State.isEqOn, Set.EqOn])
          rw[this]
          grind
        .
          intros h r
          have := Subst.admissible_adjoint.formula (U := {.var x}) (Φ := Φ) (i := i) (σ := σ)
                                                   (v := v) (w := v.update x r)
                                                   (by simp_all[Subst.admissible])
                                                   (by simp_all[State.isEqOn, Set.EqOn])
          rw[this] at h
          have := (Subst.preserve_semantics.formula σ i (v.update x r) Φ Φ' (by grind)).mpr (h r)
          grind
      | .exists x Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        .
          intros h
          obtain ⟨r, hr⟩ := h
          apply Exists.intro r

          have := Subst.preserve_semantics.formula σ i (v.update x r) Φ Φ' (by grind)
          have := Subst.admissible_adjoint.formula (U := {.var x}) (Φ := Φ) (i := i) (σ := σ)
                                                   (v := v) (w := v.update x r)
                                                   (by simp_all[Subst.admissible])
                                                   (by simp_all[State.isEqOn, Set.EqOn])
          grind
        .
          intros h
          obtain ⟨r, hr⟩ := h
          apply Exists.intro r

          have := Subst.preserve_semantics.formula σ i (v.update x r) Φ Φ' (by grind)
          have := Subst.admissible_adjoint.formula (U := {.var x}) (Φ := Φ) (i := i) (σ := σ)
                                                   (v := v) (w := v.update x r)
                                                   (by simp_all[Subst.admissible])
                                                   (by simp_all[State.isEqOn, Set.EqOn])
          grind
      | .box α Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        rename Program => α'
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        all_goals
        -- guard <| σ.admissible σα.boundVars' Φ.signature
        intros h₁ w h₂
        have := Program.bound_effect h₂
        have := Subst.preserve_semantics.program σ i v w α α'
        have := Subst.admissible_adjoint.formula (U := α'.boundVars')
                                                 (Φ := Φ) (i := i)
                                                 (σ := σ) (v := v) (w := w)
                                                 (by simp_all[Subst.admissible])
                                                 (by grind[Program.bound_effect'])
        have := Subst.preserve_semantics.formula σ i w Φ Φ'
        grind
      | .diamond α Φ =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        rename Program => α'
        rename Formula => Φ'
        simp_all[Formula.denote]
        apply Iff.intro
        all_goals
        intros h
        obtain ⟨w, hw⟩ := h
        apply Exists.intro w
        have := Subst.preserve_semantics.program σ i v w α α'
        have := Subst.admissible_adjoint.formula (U := α'.boundVars')
                                               (Φ := Φ) (i := i)
                                               (σ := σ) (v := v) (w := w)
                                               (by simp_all[Subst.admissible])
                                               (by grind[Program.bound_effect'])
        have := Subst.preserve_semantics.formula σ i w Φ Φ'
        grind
      | .ref α β =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all[Formula.denote]
        next _ _ α' _ _ _ β' _ =>
        apply Iff.intro
        all_goals
        intros h₁ w h₂
        have := Subst.preserve_semantics.program σ i v w α α'
        have := Subst.preserve_semantics.program σ i v w β β'
        grind
      | .applyPred p args =>
        simp_all[Formula.denote, Formula.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all

        next _ args' _ =>
        have : (fun (x : Fin p.arity) => Term.denote (σ.adjoint i v) v args.toVector[↑(x : ℕ)])
             = (fun (x : Fin p.arity) => Term.denote i v args'.toVector[↑x]) := by
                  funext x
                  apply Eq.symm
                  apply Subst.preserve_semantics.term _ ∅ _ _ _ (Set.eqOn_refl _ _)
                  apply Eq.symm
                  apply Subst.apply_subst_term_vector_to_term
                  assumption

        split at hs
        .
          -- we do apply the subst
          apply Subst.preserve_semantics.formula (σ := args'.toSubst) (v := v) (i := i) at hs
          rw[hs]
          rw[subst_adjoint_of_term_vector_to_subst]
          simp_all[Subst.adjoint]
        .
          -- we dont apply the subst
          have := @Subst.adjoint_noeffect_nomem_pred i v p σ (by assumption)
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
  (i : Interpretation)
  (v w : State)
  (α α' : Program)
  (hs : α' = Program.applySubst σ α)
  : ⟨v, w⟩ ∈ Program.denote i α' ↔ ⟨v, w⟩ ∈ Program.denote (Subst.adjoint σ i v) α := by
    match α with
      | .const a =>
        simp_all[Program.denote, Program.applySubst, Subst.adjoint]
      | .assign x t =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        rename Term => t'
        simp_all[Program.denote]
        have := Subst.preserve_semantics.term σ ∅ i v _ (Set.eqOn_refl _ _) t t'
        grind
      | .random x =>
        simp[Program.applySubst] at hs
        rw[hs]
        simp only [Program.denote]
      | .test Φ =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        rename Formula => Φ'
        simp_all[Program.denote]
        have := Subst.preserve_semantics.formula σ i v Φ Φ'
        grind
      | .choice α β =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all[Program.denote]
        next _ _ _ α' _ _ _ β' _ =>
        have := Subst.preserve_semantics.program σ i v w α α'
        have := Subst.preserve_semantics.program σ i v w β β'
        grind
      | .seq α β =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        split at hs
        . contradiction
        simp_all[Program.denote]
        next α' _ _ _ _ _ _ β' _ _  =>
        apply Iff.intro
        .
          intros h
          obtain ⟨w', hw'⟩ := h
          apply Exists.intro w'
          and_intros
          .
            have := Subst.preserve_semantics.program σ i v w' α α'
            grind
          .
            have := Subst.preserve_semantics.program σ i w' w β β'
            have := Subst.admissible_adjoint.program (U := α'.boundVars')
                                                     (α := β) (i := i)
                                                     (σ := σ) (v := v) (w := w')
                                                     (by simp_all[Subst.admissible])
                                                     (by grind[Program.bound_effect'])

            grind
        .
          intros h
          obtain ⟨w', hw'⟩ := h
          apply Exists.intro w'
          and_intros
          .
            have := Subst.preserve_semantics.program σ i v w' α α'
            grind
          .
            have := Subst.preserve_semantics.program σ i v w' α α'
            have := Subst.preserve_semantics.program σ i w' w β β'
            have := Subst.admissible_adjoint.program (U := α'.boundVars')
                                                     (α := β) (i := i)
                                                     (σ := σ) (v := v) (w := w')
                                                     (by simp_all[Subst.admissible])
                                                     (by grind[Program.bound_effect'])

            grind
      | .loop α =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        rename Program => α'
        simp_all[Program.denote]
        have := Subst.preserve_semantics.program σ i v w α α'
        apply Iff.intro
        .
          intros h
          induction h with
            | rfl => grind[LoopClosure]
            | trans v w h₁ h₂ ih =>
                have := ih (by apply Subst.preserve_semantics.program)
                apply LoopClosure.trans (v := v)
                . grind
                .
                  next u _ _ _ _ _ _ _ _ _ _ _ =>
                  have := (Subst.preserve_semantics.program σ i v w α α' (by grind)).mp h₂
                  have := Subst.admissible_adjoint.program (U := α'.boundVars') (α := α) (i := i)
                                                           (σ := σ) (v := u) (w := v)
                            (by simp_all[Subst.admissible])
                            (by grind)

                  simp_all[Membership.mem, Set.Mem]
        .
          intros h
          induction h with
            | rfl => grind[LoopClosure]
            | trans v w h₁ h₂ ih =>
              have := ih (by apply Subst.preserve_semantics.program)
              apply LoopClosure.trans (v := v)
              . grind
              .
                next u _ _ _ _ _ _ _ _ _ _ _ =>
                have := Subst.admissible_adjoint.program (U := α'.boundVars') (α := α) (i := i)
                                                         (σ := σ) (v := u) (w := v)
                         (by simp_all[Subst.admissible])
                         (by grind)

                have := (Subst.preserve_semantics.program σ i v w α α' (by grind)).mpr
                  (by rw[← this] ; exact h₂)

                simp_all[Membership.mem, Set.Mem]
      | .ode system Ψ =>
        simp[Program.applySubst, Option.bind] at hs
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        simp_all
        split at hs
        . contradiction
        rename List ODE => ssystem
        rename Formula => Ψ'
        simp_all[Program.denote]

        have hassign : OdeSystem.assignables ssystem = OdeSystem.assignables system :=
          ode_mapM_assignables_eq (show _ = some ssystem from ‹_›)

        rw[hassign]
        apply Iff.intro
        . rintro ⟨r, hr, φ, heq0, heqr, hflow⟩
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
                          (σ := σ) (system := system) (ssystem := ssystem)
                          (Ψ := Ψ) (Ψ' := Ψ') (by grind) (by grind)

                have := Subst.preserve_semantics.formula σ i (φ ζ)
                          (odeEvolutionFormula system Ψ)
                          (odeEvolutionFormula ssystem Ψ') (by grind)

                have := this.mp (by grind)

                have := ode_evolution_formula_admissible σ system Ψ
                          (.Finite (system.assignables ∪ system.assignables.map Assignable.diff_emb))
                          (by simp_all[Subst.admissible, OdeSystem.assignables])
                          (by simp_all[Subst.admissible, OdeSystem.assignables])

                have := Subst.admissible_adjoint.formula
                          (v := v) (w := φ ζ) (σ := σ)
                          (i := i) (Φ := odeEvolutionFormula system Ψ)
                          (U := .Finite (system.assignables ∪ system.assignables.map Assignable.diff_emb))
                          (by simp_all [Subst.admissible])
                          (by simp_all[State.isEqOn, State.isEqExcept, Set.EqOn])

                grind
              . grind
              . grind
        . rintro ⟨r, hr, φ, heq0, heqr, hflow⟩
          apply Exists.intro r
          and_intros
          . grind
          .
            apply Exists.intro φ
            and_intros
            . grind
            . grind
            .
              intros ζ h₁ h₂
              and_intros
              .
                have := hflow ζ h₁ h₂

                have := ode_evolution_formula_applySubst
                          (σ := σ) (system := system) (ssystem := ssystem)
                          (Ψ := Ψ) (Ψ' := Ψ') (by grind) (by grind)

                have := Subst.preserve_semantics.formula σ i (φ ζ)
                          (odeEvolutionFormula system Ψ)
                          (odeEvolutionFormula ssystem Ψ') (by grind)

                have := ode_evolution_formula_admissible σ system Ψ
                          (.Finite (system.assignables ∪ system.assignables.map Assignable.diff_emb))
                          (by simp_all[Subst.admissible, OdeSystem.assignables])
                          (by simp_all[Subst.admissible, OdeSystem.assignables])

                have := Subst.admissible_adjoint.formula
                          (v := v) (w := φ ζ) (σ := σ)
                          (i := i) (Φ := odeEvolutionFormula system Ψ)
                          (U := .Finite (system.assignables ∪ system.assignables.map Assignable.diff_emb))
                          (by simp_all [Subst.admissible])
                          (by simp_all [State.isEqOn, State.isEqExcept, Set.EqOn])

                grind
              . grind
              . grind
termination_by (σ.size, α.size)
decreasing_by
  all_goals simp[Prod.lex_def, Program.size]
  all_goals grind[ode_evolution_formula_size_bound]

end

-- Uniform Substitution for Differential Dynamic Logic is sound!
theorem US {σ : Subst} {Φ Φ' : Formula}
  : Formula.applySubst σ Φ = Φ'
  → (∀ (i : Interpretation) (v : State), v ∈ Formula.denote i Φ)
  → (∀ (i : Interpretation) (v : State), v ∈ Formula.denote i Φ') := by
  intros h₁ h₂ i v
  have := h₂ i v
  have := Subst.preserve_semantics.formula σ i v Φ Φ' (by grind)
  simp_all

theorem US_rule {σ : Subst}
                (premises : List (Formula × Formula))
                (Ψ Ψ' : Formula)
                (hp : ∀ Φ ∈ premises, Formula.applySubst σ Φ.1 = Φ.2)
                (hΨ : Formula.applySubst σ Ψ = Ψ')
                (hσ : Subst.freeVars σ .none = ∅)
  : (∀ (i : Interpretation), (∀ (v : State) (Φ : Formula × Formula), Φ ∈ premises → v ∈ Formula.denote i Φ.1) → (∀ (v : State), v ∈ Formula.denote i Ψ))
  → (∀ (i : Interpretation), (∀ (v : State) (Φ : Formula × Formula), Φ ∈ premises → v ∈ Formula.denote i Φ.2) → (∀ (v : State), v ∈ Formula.denote i Ψ')) := by
  intros h₁ i h₂ v

  have := by
    apply h₁ (Subst.adjoint σ i v) (?_) v
    intros w Φ hp
    have := Subst.preserve_semantics.formula σ i w Φ.1 Φ.2 (by grind)
    have := Subst.freeVars_symbol_subset_none (σ := σ) (S := (Φ.1).signature)
    have := Subst.admissible_adjoint.formula
              (Φ := Φ.1) (i := i) (σ := σ)
              (v := v) (w := w) (U := .univ)
              (by simp_all [Subst.admissible])
              (by simp_all)
    grind

  have := Subst.preserve_semantics.formula σ i v Ψ Ψ' (by grind)
  grind
