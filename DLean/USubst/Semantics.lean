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

theorem Subst.preserve_semantics_fn (σ : Subst)
            {n : ℕ}
            (args args' : TermVector n)
            (t t' : Term)
            (f : FunctionSymbol)
  : Option.some t' = Term.applySubst (TermVector.toSubst args') (Subst.get σ (Symbol.Function f))
  → Term.denote i v t'
  = Term.denote (i.assignDots fun x ↦ Term.denote (σ.adjoint i v) v args.toVector[↑x])
                v
                (σ.get (Symbol.Function f)) := by
  intro h
  match hc : t' with
    | .var x =>
      sorry
    | .neg t₁ =>

      sorry
    | _ => sorry

#check Option.some_eq_dite_none_left

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
            -- we do apply the subst
            split at hs
            . contradiction
            next a b c d =>
            simp_all

            simp[Term.denote, Subst.adjoint]

            apply Subst.preserve_semantics_fn
            . assumption
            . exact hs
          .
            -- we don't apply subst
            simp_all
            apply Eq.symm
            apply Subst.adjoint_noeffect_nomem
            . assumption
            . assumption


          -- trash from last proof attempt
          split at hs
          . contradiction
          next args heq =>
          match σ with
            | ⟨.nil, _⟩ =>
              match hs : s with
                | .dot n => simp_all[Subst.get, Subst.adjoint, Term.denote]
                | .udef name arity =>
                  simp_all
                  simp[Subst.get, Symbol.default]
                  rw[Subst.adjoint_nil]
            | ⟨e::es, hsubst⟩ =>
              let σ' : Subst := ⟨es, Subst.tail_nodup hsubst⟩

              match e with
                | .fn f' rhs =>
                  match s with
                    | .dot n =>
                      by_cases hc : (.dot n) = f'
                      .
                        cases hc
                        simp at hs
                        rw[hs]
                        have := @Subst.get_fn_head ⟨es, Subst.tail_nodup hsubst⟩ (.dot n) rhs (by simp[*])
                        rw[this]
                        simp[Term.denote]
                        simp[Subst.adjoint]
                        rw[this]
                      .
                        have := @Subst.get_tail
                              ⟨es, Subst.tail_nodup hsubst⟩
                              (.Function (.dot n))
                              (.fn f' rhs)
                              (by simp_all)
                              (by simp[*, SubstEntry.symbol])
                        apply Subst.preserve_semantics.term
                        simp_all[Term.applySubst]
                    | .udef _ _ => sorry
                | .pred p rhs =>
                  rw[@Subst.adjoint_term_noeffect.pred i p rhs es hsubst]
                  apply Subst.preserve_semantics.term
                  have := @Subst.get_tail
                          ⟨es, Subst.tail_nodup hsubst⟩
                          (.Function s)
                          (.pred p rhs)
                          (by simp_all)
                          (by simp[SubstEntry.symbol])
                  match hs : s with
                    | .dot n =>
                      simp_all
                      rfl
                    | .udef name arity =>
                      rw[TermVector.apply_subst_noeffect.pred] at heq
                      simp_all[Term.applySubst, Option.bind]
                | .prog a rhs =>
                  rw[@Subst.adjoint_term_noeffect.prog i a rhs es hsubst]
                  apply Subst.preserve_semantics.term
                  have := @Subst.get_tail
                          ⟨es, Subst.tail_nodup hsubst⟩
                          (.Function s)
                          (.prog a rhs)
                          (by simp_all)
                          (by simp[SubstEntry.symbol])
                  match hs : s with
                    | .dot n =>
                      simp_all
                      rfl
                    | .udef name arity =>
                      rw[TermVector.apply_subst_noeffect.prog] at heq
                      simp_all[Term.applySubst, Option.bind]
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
