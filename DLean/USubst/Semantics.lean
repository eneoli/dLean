import DLean.USubst.Subst
import DLean.Semantics.State
import DLean.Semantics.Interpretation

open Semantics

-- Unused
theorem Subst.adjoint_term_noeffect.pred
  (i : Interpretation)
  (p : PredicateSymbol)
  {rhs : TermVector p.arity → Formula}
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
              simp_all[Term.denote, Subst.adjoint]
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
        apply Subtype.eq
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
  = Formula.applyPred p := by
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
  = (i.assignDots fun x ↦ Term.denote i v args.toVector[↑x]) := by
    funext s
    match s with
      | .Function f =>
        simp[Subst.adjoint]

        match f with
          | .dot m =>
            by_cases m < n
            .
              have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
                   = args.toVector[m] := by
                    apply term_vector_to_subst_get.dot.mem args 0 m (by omega) (by omega)
              simp only [this]

              apply Subtype.eq
              funext args'
              simp_all
              simp_all[Interpretation.assignDots]
            .
              have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
                   = Term.dot m := by
                    simp[TermVector.toSubst]
                    apply term_vector_to_subst_get.dot.nomem m args 0 (by omega)
              simp only [this]

              simp_all
              simp_all[Interpretation.assignDots]
              split
              . grind
              .
                simp_all[Term.dot, Term.denote, FunctionSymbol.arity, TermVector.toVector]
                apply Subtype.eq
                funext args
                simp_all

                have : args = fun x ↦ [][↑x] := by grind
                simp[this]
          | .udef f' a =>
            simp only [TermVector.toSubst, term_vector_to_subst_get.fn, Symbol.default]

            apply Subtype.eq
            funext args
            simp_all[Term.denote, FunctionSymbol.arity]
            have : ∀ (x : Fin a), (Term.dots a).toVector[(↑x : ℕ)]
             = Term.dot x := by
                apply Interpretation.dots_eq
            simp only [this]
            simp_all[Term.dot, Term.denote, TermVector.toVector, Interpretation.assignDots]
      | .Predicate p =>
        simp[Subst.adjoint]

        simp only [TermVector.toSubst, term_vector_to_subst_get.pred]

        funext args
        simp_all[Formula.denote]

        have : ∀ (x : Fin p.arity), (Term.dots p.arity).toVector[(↑x : ℕ)]
             = Term.dot x := by
                apply Interpretation.dots_eq

        simp only [this]

        simp[Term.dot, Term.denote, Interpretation.assignDots]
      | .Program a =>
        simp[Subst.adjoint]
        simp only [TermVector.toSubst, term_vector_to_subst_get.program]
        simp[Program.denote, Interpretation.assignDots]

theorem Subst.apply_subst_term_vector_to_term
  (σ : Subst)
  {n : ℕ}
  (args a : TermVector n)
  (x : Fin n)
  : TermVector.applySubst σ args = some a
  → Term.applySubst σ args.toVector[x] = some a.toVector[x] := by
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

theorem TermVector.freeVars_applySubst_subset {n : ℕ} (σ : Subst) (ts as : TermVector n)
  : TermVector.applySubst σ ts = some as
  → ↑as.freeVars ⊆ ↑ts.freeVars ∪ (σ.freeVars (some ts.signature)).toSet := by
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
      have := Term.freeVars_applySubst_subset σ t a heqa
      have := TermVector.freeVars_applySubst_subset σ ts' as' heqas'
      grind only [= Set.mem_union, = Set.subset_def]
termination_by (σ.size, sizeOf ts)
decreasing_by
all_goals simp_wf
all_goals grind only [= Prod.lex_def]

theorem Term.freeVars_applySubst_subset (σ : Subst) (t a : Term)
  : Term.applySubst σ t = some a
  → ↑a.freeVars ⊆ ↑t.freeVars ∪ (σ.freeVars (some t.signature)).toSet := by
  intro h₁
  match t with
  | .var v => simp_all[Term.applySubst]
  | .neg t =>
    simp_all[Term.applySubst, Option.bind]
    split at h₁
    . contradiction
    next a' heq =>
    have := Term.freeVars_applySubst_subset σ t a' heq
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
    have := Term.freeVars_applySubst_subset σ t₁ b heqb
    have := Term.freeVars_applySubst_subset σ t₂ c heqc
    simp[Term.freeVars]
    all_goals
    simp at h₁
    rw[← h₁]
    simp[Term.freeVars]
    have := @Subst.freeVars_symbol_union σ t₁.signature t₂.signature
    grind only [= Set.mem_union, = Set.subset_def]
  | .applyFn f args =>
    match f with
    | .num n =>
      simp[Term.applySubst, Option.bind] at h₁
      split at h₁
      . contradiction
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
          have := TermVector.freeVars_applySubst_subset σ args a' (by assumption)
          have := Term.freeVars_applySubst_subset a'.toSubst (σ.get (Symbol.Function s)) a h₁
          have := @toSubst.freeVars_inc _ a' (some (Term.signature (σ.get (Symbol.Function s))))
          have := @Subst.freeVars_symbol_union σ (Function.signature (Fn.sym s)) args.signature
          have := @Subst.free_vars_subset_fun σ s
          grind only [= Set.mem_union, = Set.subset_def, FCSet.to_set_eq]
        .
          simp at h₁
          rw[← h₁]
          simp[Term.freeVars]
          have := TermVector.freeVars_applySubst_subset σ args a' (by assumption)
          have := @Subst.freeVars_symbol_union σ
          grind only [= Set.mem_union, = Set.subset_def]

  | .differential t =>
    simp[Term.applySubst, Option.bind] at h₁
    split at h₁
    . contradiction
    simp at h₁
    split at h₁
    . contradiction
    next _ _ hg _ _ a' heq =>
      simp at h₁ hg
      rw[←h₁]
      clear h₁
      have := Term.freeVars_applySubst_subset σ _ _ heq
      simp only [Term.freeVars, Finset.coe_union, Finset.coe_map, Term.signature]
      grind only [= Set.mem_image, = Set.mem_empty_iff_false, = Set.mem_union, = Set.subset_def]

termination_by (σ.size, sizeOf t)
decreasing_by
all_goals simp_wf
all_goals (try grind only [= Prod.lex_def])
next hin =>
  rw[TermVector.toSubst_size]
  apply Subst.symbol_size at hin
  grind only [= Prod.lex_def]
end

theorem Term.freeVars_applySubst_admissible_univ_subset (σ : Subst) (t a : Term)
  : Term.applySubst σ t = some a
  → σ.admissible FCSet.univ t.signature
  → (a.freeVars : Set Assignable ) ⊆ (t.freeVars : Set Assignable) := by
  intros h _
  have := Term.freeVars_applySubst_subset σ t a h
  simp_all only [FCSet.to_set_eq, FCSet.to_set_inter, FCSet.to_set_univ, Set.inter_univ,
    FCSet.to_set_empty, Set.union_empty, Finset.coe_subset]


theorem Subst.preserve_semantics.term
  (σ : Subst)
  (i : Interpretation)
  (v : State)
  (t t' : Term)
  (hs : t' = Term.applySubst σ t)
  : Term.denote i v t' = Term.denote (Subst.adjoint σ i v) v t := by
  match t with
    | .var x => simp_all[Term.applySubst, Term.denote]
    | .neg t =>
      simp[Term.applySubst, Option.bind] at hs
      split at hs
      . contradiction
      .
        next a heq =>
        have := Subst.preserve_semantics.term σ i v t a (by simp[heq])
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
          have := Subst.preserve_semantics.term σ i v t₁ a (by simp[ha])
          have := Subst.preserve_semantics.term σ i v t₂ b (by simp[hb])
          simp_all[Term.denote]
    | .applyFn f args =>
      match hf : f with
        | .num n =>
          simp[Term.applySubst, Option.bind] at hs
          split at hs
          . contradiction
          simp_all[Term.denote]
        | .sym s =>
          simp[Term.applySubst, Option.bind] at hs
          split at hs
          .
            contradiction
          .
            simp_all
            -- we do apply the subst
            split at hs
            next _ b _ _ =>

              simp[Term.denote]

              -- remove adjoint by Subst.preserve_semantics.termVector
              have : (fun (x : Fin s.arity) =>
                        Term.denote (σ.adjoint i v) v args.toVector[↑(x : Nat)])
                   = (fun (x : Fin s.arity) => Term.denote i v b.toVector[↑x]) := by
                    funext x
                    apply Eq.symm
                    apply Subst.preserve_semantics.term
                    apply Eq.symm
                    apply Subst.apply_subst_term_vector_to_term
                    assumption
              rw[this]

              apply Subst.preserve_semantics.term b.toSubst at hs
              rw[hs]
              rw[subst_adjoint_of_term_vector_to_subst]
              simp only [Fin.getElem_fin, adjoint]

            next a _ _ =>
              -- we don't apply subst
              simp_all

              -- remove adjoint by Subst.preserve_semantics.termVector
              have : (fun (x : Fin s.arity) =>
                        Term.denote (σ.adjoint i v) v args.toVector[↑(x : ℕ)])
                   = (fun (x : Fin s.arity) => Term.denote i v a.toVector[↑x]) := by
                    funext x
                    apply Eq.symm
                    apply Subst.preserve_semantics.term
                    apply Eq.symm
                    apply Subst.apply_subst_term_vector_to_term
                    assumption

              simp[Term.denote]
              rw[this]

              -- remove remaining adjoint because `σ.adjoint i v f = i f` if `f ∉ σ`
              have := @Subst.adjoint_noeffect_nomem_fun i v s σ (by assumption)
              rw[this]
              simp
    | .differential t =>
      simp[Term.applySubst, Option.bind] at hs
      split at hs
      . contradiction
      simp at hs
      split at hs
      . contradiction
      next _ _ hg _ _ a heq =>
      simp at hs
      rw[hs]
      simp[Term.denote]

      have : ∀ x ∈ (t.freeVars \ a.freeVars),
        (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x) = 0 := by
        intro x hx
        apply mul_eq_zero_of_right

        have : x ∉ a.freeVars := by grind

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
              (σ := σ) t a heq (by simp_all[Subst.admissible])
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
      cases hs
      have := by
        apply @Subst.admissible_adjoint.term v (v.update x y) (v.update x y) σ i t FCSet.univ
        . simp_all only [Subst.admissible, Option.guard_eq_some']
        . simp_all[State.isEqOn]
      rw[this]

      apply Subst.preserve_semantics.term σ i (v.update x y)
      grind
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
