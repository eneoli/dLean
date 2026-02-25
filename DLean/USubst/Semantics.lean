import DLean.USubst.Subst
import DLean.Semantics.State
import DLean.Semantics.Interpretation

open Semantics

-- variable (i : Interpretation) (v : State)

-- theorem Subst.adjoint_term_noeffect.pred
--         (p : PredicateSymbol)
--         {rhs : TermVector p.arity → Formula}
--         {es : List SubstEntry}
--         (hsubst : Subst.Nodup (SubstEntry.pred p rhs :: es))
--         (t : Term)
--         (v : State)
--         (w : State)
--   : Term.denote (Subst.adjoint ⟨SubstEntry.pred p rhs :: es, hsubst⟩ i v) w t
--   = Term.denote (Subst.adjoint ⟨es, Subst.tail_nodup hsubst⟩ i v) w t := by
--   match t with
--     | .var x => simp[Term.denote]
--     | .neg t' =>
--       have := @Subst.adjoint_term_noeffect.pred p rhs es hsubst t'
--       simp_all only [Term.denote]
--     | .plus t₁ t₂
--     | .times t₁ t₂ =>
--       have := @Subst.adjoint_term_noeffect.pred p rhs es hsubst t₁
--       have := @Subst.adjoint_term_noeffect.pred p rhs es hsubst t₂
--       simp_all only [Term.denote]
--     | .applyFn f args =>
--       match f with
--         | .num n => simp[Term.denote]
--         | .sym f =>
--           match f with
--             | .dot n =>
--               have := @Subst.get_tail
--                         ⟨es, Subst.tail_nodup hsubst⟩
--                         (.Function (.dot n))
--                         (.pred p rhs)
--                         (by simp_all)
--                         (by simp[SubstEntry.symbol])
--               simp_all[Term.denote, Subst.adjoint]
--             | .udef name arity =>
--               simp[Term.denote, Subst.adjoint]
--               congr 1
--               .
--                 congr
--                 funext x
--                 apply Subst.adjoint_term_noeffect.pred
--               .
--                 have := @Subst.get_tail
--                           ⟨es, Subst.tail_nodup hsubst⟩
--                           (.Function (.udef name arity))
--                           (.pred p rhs)
--                           (by simp_all)
--                           (by simp[SubstEntry.symbol])

--                 rw[this]
--     | .differential t =>
--       simp[Term.denote]
--       apply Finset.sum_equiv (by rfl) (fun i ↦ by rfl)
--       intros
--       congr
--       funext
--       apply Subst.adjoint_term_noeffect.pred
-- decreasing_by
--   all_goals try decreasing_trivial
--     -- TODO automate this?
--   have ha : sizeOf args.toVector[x] < sizeOf args := by
--     apply TermVector.sizeOf_lt_of_mem
--     simp[TermVector.mem_toVector_iff]

--   have hb : sizeOf args < sizeOf (Term.applyFn (.sym (FunctionSymbol.udef name arity)) args) := by simp
--   grind

-- theorem Subst.adjoint_term_noeffect.prog
--         (a : ProgramSymbol)
--         {rhs : Program}
--         {es : List SubstEntry}
--         (hsubst : Subst.Nodup (SubstEntry.prog a rhs :: es))
--         (t : Term)
--         (v : State)
--         (w : State)
--   : Term.denote (Subst.adjoint ⟨SubstEntry.prog a rhs :: es, hsubst⟩ i v) w t
--   = Term.denote (Subst.adjoint ⟨es, Subst.tail_nodup hsubst⟩ i v) w t := by
--   sorry


-- theorem TermVector.apply_subst_noeffect.pred
--         (p : PredicateSymbol)
--         {rhs : TermVector p.arity → Formula}
--         {es : List SubstEntry}
--         (hsubst : Subst.Nodup (SubstEntry.pred p rhs :: es))
--         {n : ℕ}
--         (ts : TermVector n)
--   : TermVector.applySubst ⟨SubstEntry.pred p rhs :: es, hsubst⟩ ts
--   = TermVector.applySubst ⟨es, Subst.tail_nodup hsubst⟩ ts := by
--   sorry

-- theorem TermVector.apply_subst_noeffect.prog
--         (a : ProgramSymbol)
--         {rhs : Program}
--         {es : List SubstEntry}
--         (hsubst : Subst.Nodup (SubstEntry.prog a rhs :: es))
--         {n : ℕ}
--         (ts : TermVector n)
--   : TermVector.applySubst ⟨SubstEntry.prog a rhs :: es, hsubst⟩ ts
--   = TermVector.applySubst ⟨es, Subst.tail_nodup hsubst⟩ ts := by
--   sorry

-- @[simp]
-- theorem TermVector.apply_subst_nil
--         (hsubst : Subst.Nodup .nil)
--         {n : ℕ}
--         (ts : TermVector n)
--   : TermVector.applySubst ⟨.nil, hsubst⟩ ts
--   = ts := by
--   sorry

-- theorem Subst.adjoint_noeffect_nomem (i : Interpretation)
--                                      (v : State)
--                                      (σ : Subst)
--                                      (f : FunctionSymbol)
--                                      (args : TermVector f.arity)
--                                      (t : Term)
--   : .Function f ∉ σ
--   → Term.denote (Subst.adjoint σ i v) v (Term.applyFn (.sym f) args)
--   = Term.denote i v (Term.applyFn (.sym f) args) := by
--   sorry

theorem Subst.adjoint_noeffect_nomem_fun (i : Interpretation)
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
               = (fun (x : Fin (FunctionSymbol.dot n).arity) ↦ Term.denote i v TermVector.nil.toVector[x]) := by
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

theorem foo.fn {n : ℕ}
               {args : TermVector n}
               {k : ℕ}
               {f : String}
               {a : ℕ}
               (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (Symbol.Function (FunctionSymbol.udef f a))
  = Term.applyFn (.sym (FunctionSymbol.udef f a)) (Term.dots ((FunctionSymbol.udef f a).arity)) := by
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
          have := @foo.fn _ as (k + 1) f a
          simp_all

theorem foo.pred {n : ℕ}
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
          have := @foo.pred _ as (k + 1) p
          simp_all

theorem foo.program {n : ℕ}
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
          have := @foo.program _ as (k + 1) a
          simp_all


theorem foo.dot₁ {n : ℕ} (m : ℕ) (args : TermVector n)
                 (k : ℕ)
                 (h₁ : m ≥ k)
                 (h₂ : m < n + k)
                 (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.get ⟨args.toSubstAux k, hs⟩ (Symbol.Function (FunctionSymbol.dot m))
  = args.toVector[m - k] := by
  cases args with
    | nil => grind
    | cons a as =>
      next n =>

      simp_all [TermVector.toSubstAux, Subst.get]
      split
      .
        next h =>
        cases h
        simp_all[SubstEntry.rhs, TermVector.toVector]
      .
        next h =>

        have : m ≥  k + 1 := by grind[SubstEntry.symbol]
        have := @foo.dot₁ n m as (k + 1) (by omega) (by omega)
        simp_all [TermVector.toSubst, TermVector.toSubstAux, TermVector.toVector]
        grind

theorem foo.dot₂ {n : ℕ} (m : ℕ) (args : TermVector n)
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
        next n h =>
        cases h
        grind
      .
        next n h =>
        apply @foo.dot₂ n m as (k + 1) (by omega)


theorem test (i : Interpretation) (v : State) {n : ℕ} {args : TermVector n}
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
                    apply @foo.dot₁ n m args 0 (by omega) (by omega)
              simp only [this]

              apply Subtype.eq
              funext args'
              simp_all
              simp_all[Interpretation.assignDots]
            .
              have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
                   = Term.dot m := by
                    simp[TermVector.toSubst]
                    apply @foo.dot₂ n m args 0 (by omega)
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
            simp only [TermVector.toSubst, foo.fn]

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

        simp only [TermVector.toSubst, foo.pred]

        funext args
        simp_all[Formula.denote]

        have : ∀ (x : Fin p.arity), (Term.dots p.arity).toVector[(↑x : ℕ)]
             = Term.dot x := by
                apply Interpretation.dots_eq

        simp only [this]

        simp[Term.dot, Term.denote, Interpretation.assignDots]
      | .Program a =>
        simp[Subst.adjoint]
        simp only [TermVector.toSubst, foo.program]
        simp[Program.denote, Interpretation.assignDots]

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


theorem moo {σ : Subst} {s : FunctionSymbol}
  : Subst.admissible σ FCSet.univ (Function.signature (.sym s))
  → (Subst.get σ (Symbol.Function s)).freeVars = ∅ := by
  intro h
  have := @Subst.admissible_get_fn_subset σ FCSet.univ {Symbol.Function s} s (by grind) h
  simp_all


theorem mirFallenKeineNamenMehrEin'
  (name : String)
  (arity : ℕ)
  {n : ℕ}
  (args : TermVector n)
  (k : ℕ)
  (hs : Subst.Nodup (args.toSubstAux k))
  : ¬ Subst.mem (⟨args.toSubstAux k, hs⟩ : Subst)
      (Symbol.Function (FunctionSymbol.udef name arity)) := by
  cases args with
    | nil =>
      simp_all [Subst.mem, TermVector.toSubstAux]
    | cons a as =>
      simp_all [Subst.mem, TermVector.toSubstAux]
      and_intros
      . grind[SubstEntry.symbol]
      .
        have := mirFallenKeineNamenMehrEin' name arity as
        simp_all

theorem mirFallenKeineNamenMehrEin (name : String) (arity : ℕ) {n : ℕ} (args : TermVector n)
  : Symbol.Function (FunctionSymbol.udef name arity) ∉ args.toSubst := by
    simp_all [Membership.mem, TermVector.toSubst]
    apply mirFallenKeineNamenMehrEin'

theorem helpMe' {n : ℕ} {args : TermVector n} {m : ℕ} (k : ℕ)
  (hs : Subst.Nodup (args.toSubstAux k))
  : Subst.mem ⟨args.toSubstAux k, hs⟩ (Symbol.Function (FunctionSymbol.dot m))
  → m < k + n := by
  intro h
  cases args with
    | nil =>
      simp_all[TermVector.toSubstAux, Subst.mem]
    | cons a as =>
      simp_all [Subst.mem, TermVector.toSubstAux, SubstEntry.symbol]
      cases h
      . grind
      .
        next n h =>
        have := @helpMe' n as m (k + 1) (by grind) (by grind)
        grind

theorem helpMe {n : ℕ} {args : TermVector n} {m : ℕ}
  : Symbol.Function (FunctionSymbol.dot m) ∈ args.toSubst
  → m < n := by
  intro h
  simp_all[TermVector.toSubst, Membership.mem]
  have := @helpMe' n args m 0 (by grind) (by grind)
  grind

mutual

theorem thisWillNeverEnd {n : ℕ} (ts ts' : TermVector n)
  : TermVector.applySubst ⟨.nil, by grind[Subst.Nodup]⟩ ts = some ts'
  → ts = ts' := by
  intro h
  cases ts with
    | nil => simp_all
    | cons t ts =>
      simp_all[TermVector.applySubst, Option.bind]
      split at h
      . contradiction
      simp at h
      split at h
      . contradiction
      simp at h
      rw[← h]

      next _ _ _ _ h₁ _ _ _ h₂ =>

      have := thisDoesNeverEnd _ _ h₁
      have := thisWillNeverEnd _ _ h₂
      grind

theorem thisDoesNeverEnd (t t' : Term)
  : Term.applySubst ⟨.nil, by grind[Subst.Nodup]⟩ t = some t'
  → t = t' := by
  intro h
  match t with
    | .var x => simp_all[Term.applySubst]
    | .neg t =>
      simp_all[Term.applySubst, Option.bind]
      split at h
      . contradiction
      next a' _ =>
      have := thisDoesNeverEnd t a'
      simp_all
    | .plus t₁ t₂
    | .times t₁ t₂ =>
      simp[Term.applySubst, Option.bind] at h
      split at h
      . contradiction
      simp_all only
      split at h
      . contradiction
      next b _ _ _ c _ =>
      simp at h
      have := thisDoesNeverEnd t₁ b
      have := thisDoesNeverEnd t₂ c
      grind
    | .differential t =>
      simp[Term.applySubst, Option.bind] at h
      split at h
      . contradiction
      split at h
      . contradiction
      next _ _ _ _ c _ =>
      simp at h
      have := thisDoesNeverEnd t c
      grind
    | .applyFn f args' =>
      match hf : f with
        | .num n =>
            simp_all[Term.applySubst, Option.bind]
            split at h
            . contradiction
            simp_all
        | .sym s =>
          cases hf
          simp_all[Term.applySubst, Option.bind]
          split at h
          . contradiction
          split at h
          . simp_all[Membership.mem, Subst.mem]
          .
            simp at h
            rw[← h]
            congr
            simp_all[Membership.mem, Subst.mem]
            apply thisWillNeverEnd
            grind

end

mutual

theorem hoo {n m m' : ℕ}
            (args : TermVector n)
            (ts : TermVector m)
            (ts' : TermVector m')
            (hm : m = m')
   : TermVector.applySubst args.toSubst ts = some (cast (by grind) ts')
   → ts'.freeVars ⊆ ts.freeVars ∪ args.freeVars := by
    intros h₁
    match ts with
      | .nil =>
        have : m' = 0 := by grind
        cases this

        have : ts' = TermVector.nil := by simp_all
        cases this

        simp_all [TermVector.freeVars_nil, TermVector.applySubst]
      | .cons t tt =>
        simp[TermVector.applySubst, Option.bind] at h₁
        split at h₁
        . contradiction
        simp at h₁
        split at h₁
        . contradiction
        simp at h₁
        next j b c d e f g h i =>
        -- rw[← h₁]
        -- simp
        have := hoo args tt h (by grind) (by grind)
        have := boo args t d (by simp_all)

        cases ts'
        . contradiction
        simp only [TermVector.freeVars_cons]

        rename (ℕ) => n'
        have : j = n' := by omega
        cases this

        grind

termination_by
  (args.toSubst.size, sizeOf ts)
decreasing_by
  all_goals try decreasing_tactic



theorem boo {n : ℕ} (args : TermVector n) (t t' : Term)
  : Term.applySubst args.toSubst t = some t'
  → t'.freeVars ⊆ t.freeVars ∪ args.freeVars := by
  intro h

  match t with
    | .var x => simp_all[Term.applySubst]
    | .neg t =>
      simp_all[Term.applySubst, Option.bind]
      split at h
      . contradiction
      next a' _ =>
      simp at h
      rw[← h]
      simp[Term.freeVars]
      have := boo args t a' (by grind)
      simp_all
    | .plus t₁ t₂
    | .times t₁ t₂ =>
      simp[Term.applySubst, Option.bind] at h
      split at h
      . contradiction
      simp_all only
      split at h
      . contradiction
      next b _ _ _ c _ =>
      have := boo args t₁ b (by grind)
      have := boo args t₂ c (by grind)
      simp[Term.freeVars]
      all_goals
      simp at h
      rw[← h]
      simp[Term.freeVars]
      grind
      | .differential t =>
      simp_all only [Term.freeVars]
      simp[Term.applySubst, Option.bind] at h
      split at h
      . contradiction
      split at h
      . contradiction
      next _ _ _ _ c _ =>
      simp at h
      rw[← h]
      simp only [Term.freeVars]

      have := boo args t c (by grind)

      -- Termination problem
      have := bar (σ := args.toSubst) t c (by grind) (by simp_all)
      have : c.freeVars ⊆ t.freeVars := by
        intros x hx
        have := this hx
        grind
      grind
    | .applyFn f args' =>
      simp_all only [Term.freeVars]
      match hf : f with
        | .num n =>
            simp_all[Term.applySubst, Option.bind]
            split at h
            . contradiction
            simp_all
            rw[← h]
            simp[Term.freeVars]
        | .sym s =>
          cases hf
          simp_all[Term.applySubst, Option.bind]
          split at h
          . contradiction
          split at h
          .
            simp at h

            match s with
              | .dot m =>
              next b c d e f =>
                -- because Symbol.Function (FunctionSymbol.dot m) ∈ args.toSubst
                have : m < n := by apply helpMe (args := args) (by grind)
                have : d = TermVector.nil := by simp_all
                cases this

                have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
                     = args.toVector[m] := by
                    simp[TermVector.toSubst]
                    apply foo.dot₁
                    . grind
                    . grind
                rw[this] at h

                have : args.toVector[m] = t' := by
                  apply thisDoesNeverEnd
                  simp_all[TermVector.toSubst, TermVector.toSubstAux]
                rw[← this]

                have : args.toVector[m].freeVars ⊆ args.freeVars := by
                  apply Term.freeVars_subset_TermVector_freeVars
                  apply (TermVector.mem_toVector_iff (args.toVector[m]) args).mpr
                  grind

                grind
              | .udef name arity => grind[mirFallenKeineNamenMehrEin]
          .
            next b c d e f =>
            simp at h
            rw[← h]
            simp[Term.freeVars]
            exact hoo args args' d (by rfl) e
termination_by
  (args.toSubst.size, sizeOf t)


-- end

-- mutual

theorem foo (σ : Subst) {n m : ℕ} (ts : TermVector n) (a : TermVector m ) (hnm : n = m)
  : TermVector.applySubst σ ts = some (cast (by grind) a)
  → σ.admissible FCSet.univ ts.signature
  → (a.freeVars : Set Assignable) ⊆ (ts.freeVars : Set Assignable) := by
  intros h₁ h₂
  match ts with
    | .nil =>

      have : m = 0 := by grind
      cases this

      have : a = TermVector.nil := by simp_all
      cases this

      simp_all [TermVector.freeVars_nil, TermVector.applySubst]
    | .cons t tt =>
      simp[TermVector.applySubst, Option.bind] at h₁
      split at h₁
      . contradiction
      simp at h₁
      split at h₁
      . contradiction
      simp at h₁

      simp only [TermVector.signature_cons] at h₂
      apply Subst.admissible_symbol_union.mp at h₂

      cases a
      . contradiction

      next b c d e f g j h i n x l =>
      have := foo σ tt h (by rfl) (by grind) (by simp_all)
      have := bar σ t e (by simp_all) (by simp_all)

      have : n =  b := by omega
      cases this

      have : e = x := by grind
      -- simp_all only [this]

      have : h = l := by grind
      -- simp only [this] at *

      simp only [TermVector.freeVars_cons]

      simp_all
      grind
termination_by
  (σ.size, sizeOf ts)
decreasing_by
  all_goals simp[Prod.lex_def]
  . omega

theorem bar (σ : Subst) (t a : Term)
  : Term.applySubst σ t = some a
  → σ.admissible FCSet.univ t.signature
  → (a.freeVars : Set Assignable ) ⊆ (t.freeVars : Set Assignable) := by
    intros h₁ h₂
    match t with
      | .var x => simp_all[Term.applySubst]
      | .neg t =>
        simp_all[Term.applySubst, Option.bind]
        split at h₁
        . contradiction
        next a' _ =>
        have := bar σ t a' (by grind) (by simp_all[Term.signature])
        simp_all
        rw[← h₁]
        simp only[Term.freeVars]
        assumption
      | .plus t₁ t₂
      | .times t₁ t₂ =>
        simp[Term.applySubst, Option.bind] at h₁
        split at h₁
        . contradiction
        simp_all only
        split at h₁
        . contradiction
        next b _ _ _ c _ =>
        simp_all only [Term.signature]
        apply Subst.admissible_symbol_union.mp at h₂
        have := bar σ t₁ b (by grind) (by grind[Term.signature])
        have := bar σ t₂ c (by grind) (by grind[Term.signature])
        simp[Term.freeVars]
        all_goals
        simp at h₁
        rw[← h₁]
        simp[Term.freeVars]
        grind
      | .applyFn (.num n) args =>
        simp_all[Term.applySubst, Option.bind]
        split at h₁
        . contradiction
        simp_all
      | .applyFn (.sym s) args =>
        simp_all only [Term.freeVars, Term.signature]
        apply Subst.admissible_symbol_union.mp at h₂
        simp[Term.applySubst, Option.bind] at h₁
        split at h₁
        . contradiction
        next a' _ =>
        split at h₁
        .
          simp at h₁


          -- ((Subst.get σ f).freeVars : Set _) ⊆ (U : Set Assignable)ᶜ

          -- this makes trouble
          have : a.freeVars ⊆ (σ.get (Symbol.Function s)).freeVars ∪ a'.freeVars := by
            apply boo (args := a')
            grind
            -- have ih := bar a'.toSubst (σ.get (Symbol.Function s)) a (.Infinite a'.freeVars) h₁ (
            --   by
            --     simp[Subst.admissible]
            --     have : (FCSet.Infinite a'.freeVars).toSet
            --          = (a'.freeVars : Set Assignable)ᶜ := by simp_all[FCSet.toSet]
            --     rw[this]

            --     have : (a'.toSubst.freeVars (some (Term.signature (σ.get (Symbol.Function s))))).toSet
            --          ⊆ (a'.toSubst.freeVars .none).toSet := sorry

            --     have : (a'.toSubst.freeVars .none).toSet ∩ (↑a'.freeVars)ᶜ = ∅ := by sorry
            --     grind
            -- )
          have : (σ.get (Symbol.Function s)).freeVars = ∅ := by
            apply moo
            grind
            -- have : (FCSet.Infinite a'.freeVars).toSetᶜ = ∅ := by simp_all[FCSet.toSet]
            -- rw[this] at ih
            -- intro x hx
            -- have := @ih x (by grind)
            -- grind


          have  := foo (σ := σ) args a' (by grind)

          have : a'.freeVars ⊆ args.freeVars := by
            apply foo (σ:= σ)
            . grind
            . grind
            . grind

          -- we should have `Term.freeVars (σ.get (Symbol.Function s))` to
          -- be the same as `(σ.freeVars (some (Function.signature s)))` (Lemma?),
          -- and thus empty, and thus included
          -- because σ.admissible FCSet.univ (Function.signature s)
          -- have : ((σ.get (Symbol.Function s)).freeVars : Set Assignable) ⊆ (S : Set Assignable)ᶜ := by
            -- have := @Subst.admissible_get_fn_subset σ S (Function.signature (.sym s)) s (by grind[Function.signature]) (by grind)
            -- grind

          -- have : (a.freeVars : Set Assignable) ⊆ a'.freeVars ∪ (S : Set Assignable)ᶜ := by grind

          grind
        .
          simp at h₁
          rw[← h₁]
          simp[Term.freeVars]
          have := foo σ args a' (by rfl) (by grind) (by grind)
          intro x hx
          have := this hx
          grind
      | .differential t =>
        simp_all only [Term.signature, Term.freeVars]
        simp[Term.applySubst, Option.bind] at h₁
        split at h₁
        . contradiction
        split at h₁
        . contradiction
        next _ _ _ _ c _ =>
        simp at h₁
        rw[← h₁]
        simp only [Term.freeVars]
        have := bar σ t c (by grind) (by simp_all[Subst.admissible])

        have ih := bar σ t c (by grind) (by simp_all[Subst.admissible])
        have : FCSet.univ.toSetᶜ = (∅ : Set Assignable) := by grind
        simp at ih
        grind
termination_by
  (σ.size, sizeOf t)
decreasing_by
  all_goals simp[Prod.lex_def]
  all_goals try omega
  .
    have := Subst.symbol_size' σ s (by assumption)
    have := @TermVector.toSubst_size s.arity
    grind

end

theorem Subst.preserve_semantics.term (σ : Subst)
                                      (i : Interpretation)
                                      (v : State)
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
            next a b c d =>

              simp[Term.denote]
              -- remove adjoint by Subst.preserve_semantics.termVector
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
              -- termination proof gets stuck here (solved)
              apply Subst.preserve_semantics.term b.toSubst at hs
              rw[hs]
              rw[test]
              simp only [Fin.getElem_fin, adjoint]

              -- apply Subst.preserve_semantics_fn
              -- . assumption
              -- . exact hs
            next a _ _ =>
              -- we don't apply subst
              simp_all

              -- remove adjoint by Subst.preserve_semantics.termVector
              have : (fun (x : Fin s.arity) => Term.denote (σ.adjoint i v) v args.toVector[↑(x : ℕ)])
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
      next _ _ hg _ _ a _ =>
      simp at hs
      -- simp at hg
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

      -- true because hg : guard (σ.admissible FCSet.univ t.signature)
      -- and hence substitution can *only reduce* free variables, e.g. {f(⋅) → 2}
      have : a.freeVars ⊆ t.freeVars := by
        have  ih := bar (σ := σ) t a (by grind) (by simp_all[Subst.admissible])
        -- have : FCSet.univ.toSetᶜ = (∅ : Set Assignable) := by grind
        -- rw[this] at ih
        intro x hx
        have := ih hx
        grind

      have : ∑ x ∈ a.freeVars, (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x)
           = ∑ x ∈ t.freeVars, (v x.diff) * deriv (fun y ↦ Term.denote i (v.update x y) a) (v x) := by
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
        . simp_all[Subst.admissible]
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
    have := Subst.symbol_size' σ s (by assumption)
    have := @TermVector.toSubst_size s.arity
    grind
