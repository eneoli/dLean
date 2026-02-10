import DLean.USubst.Subst
import DLean.Semantics.State
import DLean.Semantics.Interpretation

open Semantics

variable (i : Interpretation) (v : State)

theorem Subst.adjoint_term_noeffect.pred
        (p : PredicateSymbol)
        {rhs : TermVector p.arity → Formula}
        {es : List SubstEntry}
        (hsubst : Subst.Nodup (SubstEntry.pred p rhs :: es))
        (t : Term)
        (v : State)
        (w : State)
  : Term.denote (Subst.adjoint ⟨SubstEntry.pred p rhs :: es, hsubst⟩ i v) w t
  = Term.denote (Subst.adjoint ⟨es, Subst.tail_nodup hsubst⟩ i v) w t := by
  match t with
    | .var x => simp[Term.denote]
    | .neg t' =>
      have := @Subst.adjoint_term_noeffect.pred p rhs es hsubst t'
      simp_all only [Term.denote]
    | .plus t₁ t₂
    | .times t₁ t₂ =>
      have := @Subst.adjoint_term_noeffect.pred p rhs es hsubst t₁
      have := @Subst.adjoint_term_noeffect.pred p rhs es hsubst t₂
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
              congr
              .
                funext x
                apply Subst.adjoint_term_noeffect.pred
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
      apply Subst.adjoint_term_noeffect.pred
decreasing_by
  all_goals try decreasing_trivial
    -- TODO automate this?
  have ha : sizeOf args.toVector[x] < sizeOf args := by
    apply TermVector.sizeOf_lt_of_mem
    simp[TermVector.mem_toVector_iff]

  have hb : sizeOf args < sizeOf (Term.applyFn (.sym (FunctionSymbol.udef name arity)) args) := by simp
  grind

theorem Subst.adjoint_term_noeffect.prog
        (a : ProgramSymbol)
        {rhs : Program}
        {es : List SubstEntry}
        (hsubst : Subst.Nodup (SubstEntry.prog a rhs :: es))
        (t : Term)
        (v : State)
        (w : State)
  : Term.denote (Subst.adjoint ⟨SubstEntry.prog a rhs :: es, hsubst⟩ i v) w t
  = Term.denote (Subst.adjoint ⟨es, Subst.tail_nodup hsubst⟩ i v) w t := by
  sorry


theorem TermVector.apply_subst_noeffect.pred
        (p : PredicateSymbol)
        {rhs : TermVector p.arity → Formula}
        {es : List SubstEntry}
        (hsubst : Subst.Nodup (SubstEntry.pred p rhs :: es))
        {n : ℕ}
        (ts : TermVector n)
  : TermVector.applySubst ⟨SubstEntry.pred p rhs :: es, hsubst⟩ ts
  = TermVector.applySubst ⟨es, Subst.tail_nodup hsubst⟩ ts := by
  sorry

theorem TermVector.apply_subst_noeffect.prog
        (a : ProgramSymbol)
        {rhs : Program}
        {es : List SubstEntry}
        (hsubst : Subst.Nodup (SubstEntry.prog a rhs :: es))
        {n : ℕ}
        (ts : TermVector n)
  : TermVector.applySubst ⟨SubstEntry.prog a rhs :: es, hsubst⟩ ts
  = TermVector.applySubst ⟨es, Subst.tail_nodup hsubst⟩ ts := by
  sorry

@[simp]
theorem TermVector.apply_subst_nil
        (hsubst : Subst.Nodup .nil)
        {n : ℕ}
        (ts : TermVector n)
  : TermVector.applySubst ⟨.nil, hsubst⟩ ts
  = ts := by
  sorry

theorem Subst.adjoint_noeffect_nomem (i : Interpretation)
                                     (v : State)
                                     (σ : Subst)
                                     (f : FunctionSymbol)
                                     (args : TermVector f.arity)
                                     (t : Term)
  : .Function f ∉ σ
  → Term.denote (Subst.adjoint σ i v) v (Term.applyFn (.sym f) args)
  = Term.denote i v (Term.applyFn (.sym f) args) := by
  sorry

-- replaced by `test` below
-- theorem Subst.preserve_semantics_fn (σ : Subst)
--             {n : ℕ}
--             (args args' : TermVector n)
--             (t t' : Term)
--             (f : FunctionSymbol)
--   : Option.some t' = Term.applySubst (TermVector.toSubst args') (Subst.get σ (Symbol.Function f))
--   → Term.denote i v t'
--   = Term.denote (i.assignDots fun x ↦ Term.denote (σ.adjoint i v) v args.toVector[↑x])
--                 v
--                 (σ.get (Symbol.Function f)) := by
--   intro h
--   match hc : t' with
--     | .var x =>
--       sorry
--     | .neg t₁ =>

--       sorry
--     | _ => sorry

theorem Subst.adjoint_noeffect_nomem_fun {f : FunctionSymbol}
                                         {σ : Subst}
  : (.Function f) ∉ σ
  → (σ.adjoint i v (Symbol.Function f)) = i f := by
    sorry

theorem test {n : ℕ} {args : TermVector n}
  : Subst.adjoint (TermVector.toSubst args) i v
  = (i.assignDots fun x ↦ Term.denote i v args.toVector[↑x]) := by
    match args with
      | .nil =>
        funext s
        match s with
          | .Function f =>
            simp[
              TermVector.toSubst,
              TermVector.toSubstAux,
              Subst.adjoint,
              Subst.get,
              Symbol.default,
            ]

            apply Subtype.eq

            funext args
            simp_all[Term.denote]




            sorry
          | .Predicate p =>
            simp[
              TermVector.toSubst,
              TermVector.toSubstAux,
              Subst.adjoint,
              Subst.get,
              Symbol.default,
            ]

            funext args
            simp_all[Formula.denote]
            sorry
          | .Program a =>
            simp[
              TermVector.toSubst,
              TermVector.toSubstAux,
              Subst.adjoint,
              Subst.get,
              Symbol.default,
              Program.denote
            ]
      | .cons a as =>
        sorry

#check Option.some_eq_dite_none_left

theorem Subst.apply_subst_term_vector_to_term (σ : Subst)
                                              (n : ℕ)
                                              (a args : TermVector n)
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

mutual

-- theorem Subst.preserve_semantics.termVector (σ : Subst)
--                                             {n : ℕ}
--                                             (ts : TermVector n)
--                                             (ts' : TermVector n)
--                                             (x : Fin n)
--                                             (hs : ts' = TermVector.applySubst σ ts)
--   : Term.denote i v ts'.toVector[x] = Term.denote (Subst.adjoint σ i v) v ts.toVector[x] := by
--     apply Subst.preserve_semantics.term
--     simp_all[TermVector.applySubst]
--     sorry

theorem Subst.preserve_semantics.term (σ : Subst)
                                      (t : Term)
                                      (t' : Term)
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
        have := Subst.preserve_semantics.term σ t a (by simp[heq])
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
          have := Subst.preserve_semantics.term σ t₁ a (by simp[ha])
          have := Subst.preserve_semantics.term σ t₂ b (by simp[hb])
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
            next a b c d =>

              simp[Term.denote]
              -- remove adjoint by Subst.preserve_semantics.termVector (TBD)
              have : (fun (x : Fin s.arity) => Term.denote (σ.adjoint i v) v args.toVector[↑(x : Nat)])
                   = (fun (x : Fin s.arity) => Term.denote i v b.toVector[↑x]) := by
                    funext x
                    apply Eq.symm
                    apply Subst.preserve_semantics.term
                    apply Eq.symm
                    apply Subst.apply_subst_term_vector_to_term
                    assumption

              rw[this]

              -- apply test theorem
              apply Subst.preserve_semantics.term at hs
              rw[hs]
              rw[test]
              simp only [Fin.getElem_fin, adjoint]

              -- apply Subst.preserve_semantics_fn
              -- . assumption
              -- . exact hs
            next a _ _ =>
              -- we don't apply subst
              simp_all

              -- remove adjoint by Subst.preserve_semantics.termVector (TBD)
              have : (fun (x : Fin s.arity) => Term.denote (σ.adjoint i v) v args.toVector[↑(x : Nat)])
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
      next hg _ _ _ _ =>
      simp at hs
      simp at hg
      rw[hs]
      simp[Term.denote]
      congr
      .
        sorry
      .
        funext x
        congr
        funext y

        -- apply Subst.admissible_adjoint.term

        sorry
termination_by
  (sizeOf σ, sizeOf t)
decreasing_by
  all_goals try decreasing_trivial
  all_goals try omega

end
