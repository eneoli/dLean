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


theorem subst_admissible_univ_free_vars {σ : Subst} {s : FunctionSymbol}
  : Subst.admissible σ FCSet.univ (Function.signature (.sym s))
  → (Subst.get σ (Symbol.Function s)).freeVars = ∅ := by
  intro h
  have := @Subst.admissible_get_fn_subset σ FCSet.univ {Symbol.Function s} s (by grind) h
  simp_all

/-- Helper -/
theorem term_vector_to_subst_nomem_fn'
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
        have := term_vector_to_subst_nomem_fn' name arity as
        simp_all

theorem term_vector_to_subst_nomem_fn (name : String) (arity : ℕ) {n : ℕ} (args : TermVector n)
  : Symbol.Function (FunctionSymbol.udef name arity) ∉ args.toSubst := by
    simp_all [Membership.mem, TermVector.toSubst]
    apply term_vector_to_subst_nomem_fn'

/-- Helper -/
theorem dot_mem_subst_idx'
  {n : ℕ}
  (args : TermVector n)
  (m k : ℕ)
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
        have := dot_mem_subst_idx' as m (k + 1) (by grind) (by grind)
        grind

theorem dot_mem_subst_idx {n : ℕ} {args : TermVector n} {m : ℕ}
  : Symbol.Function (FunctionSymbol.dot m) ∈ args.toSubst
  → m < n := by
  intro h
  simp_all[TermVector.toSubst, Membership.mem]
  have := dot_mem_subst_idx' args m 0 (by grind) (by grind)
  grind

mutual

theorem TermVector.applySubst_empty_eq {n : ℕ} (ts ts' : TermVector n)
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

      have := Term.applySubst_empty_eq _ _ h₁
      have := TermVector.applySubst_empty_eq _ _ h₂
      grind

theorem Term.applySubst_empty_eq (t t' : Term)
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
      have := Term.applySubst_empty_eq t a'
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
      have := Term.applySubst_empty_eq t₁ b
      have := Term.applySubst_empty_eq t₂ c
      grind
    | .differential t =>
      simp[Term.applySubst, Option.bind] at h
      split at h
      . contradiction
      split at h
      . contradiction
      next _ _ _ _ c _ =>
      simp at h
      have := Term.applySubst_empty_eq t c
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
            apply TermVector.applySubst_empty_eq
            grind

end

mutual

theorem TermVector.freeVars_applySubst_toSubst_subset
  {n m m' : ℕ}
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
        next j _ _ d _ _ _ h _ =>
        have := TermVector.freeVars_applySubst_toSubst_subset args tt h (by grind) (by grind)
        have := Term.freeVars_applySubst_toSubst_subset args t d (by simp_all)

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

theorem Term.freeVars_applySubst_toSubst_subset
  {n : ℕ}
  (args : TermVector n)
  (t t' : Term)
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
      have := Term.freeVars_applySubst_toSubst_subset args t a' (by grind)
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
      have := Term.freeVars_applySubst_toSubst_subset args t₁ b (by grind)
      have := Term.freeVars_applySubst_toSubst_subset args t₂ c (by grind)
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

      have := Term.freeVars_applySubst_toSubst_subset args t c (by grind)

      have := Term.freeVars_applySubst_admissible_subset
                (σ := args.toSubst) t c (by grind) (by simp_all)
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
              next _ _ d _ _ =>
                -- because Symbol.Function (FunctionSymbol.dot m) ∈ args.toSubst
                have : m < n := by apply dot_mem_subst_idx (args := args) (by grind)
                have : d = TermVector.nil := by simp_all
                cases this

                have : args.toSubst.get (Symbol.Function (FunctionSymbol.dot m))
                     = args.toVector[m] := by
                    simp[TermVector.toSubst]
                    apply term_vector_to_subst_get.dot.mem
                    . grind
                    . grind
                rw[this] at h

                have : args.toVector[m] = t' := by
                  apply Term.applySubst_empty_eq
                  simp_all[TermVector.toSubst, TermVector.toSubstAux]
                rw[← this]

                have : args.toVector[m].freeVars ⊆ args.freeVars := by
                  apply Term.freeVars_subset_TermVector_freeVars
                  apply (TermVector.mem_toVector_iff (args.toVector[m]) args).mpr
                  grind

                grind
              | .udef name arity => grind[term_vector_to_subst_nomem_fn]
          .
            next _ _ d e _ =>
            simp at h
            rw[← h]
            simp[Term.freeVars]
            exact TermVector.freeVars_applySubst_toSubst_subset args args' d (by rfl) e
termination_by
  (args.toSubst.size, sizeOf t)

theorem TermVector.freeVars_applySubst_admissible_subset
  (σ : Subst)
  {n m : ℕ}
  (ts : TermVector n)
  (a : TermVector m)
  (hnm : n = m)
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

      next b _ _ e _ _ _ h _ n x l =>
      have := TermVector.freeVars_applySubst_admissible_subset
                σ tt h (by rfl) (by grind) (by simp_all)
      have := Term.freeVars_applySubst_admissible_subset σ t e (by simp_all) (by simp_all)

      have : n =  b := by omega
      cases this

      have : e = x := by grind
      have : h = l := by grind

      simp_all[TermVector.freeVars_cons]
      grind
termination_by
  (σ.size, sizeOf ts)
decreasing_by
  all_goals simp[Prod.lex_def]
  . omega

theorem Term.freeVars_applySubst_admissible_subset
  (σ : Subst)
  (t a : Term)
  : Term.applySubst σ t = some a
  → σ.admissible FCSet.univ t.signature
  → (a.freeVars : Set Assignable) ⊆ (t.freeVars : Set Assignable) := by
    intros h₁ h₂
    match t with
      | .var x => simp_all[Term.applySubst]
      | .neg t =>
        simp_all[Term.applySubst, Option.bind]
        split at h₁
        . contradiction
        next a' _ =>
        have := Term.freeVars_applySubst_admissible_subset
                  σ t a' (by grind) (by simp_all[Term.signature])
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
        have := Term.freeVars_applySubst_admissible_subset
                  σ t₁ b (by grind) (by grind[Term.signature])
        have := Term.freeVars_applySubst_admissible_subset
          σ t₂ c (by grind) (by grind[Term.signature])
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

          have : a.freeVars ⊆ (σ.get (Symbol.Function s)).freeVars ∪ a'.freeVars := by
            apply Term.freeVars_applySubst_toSubst_subset (args := a')
            grind

          have : (σ.get (Symbol.Function s)).freeVars = ∅ := by
            apply subst_admissible_univ_free_vars
            grind

          have := TermVector.freeVars_applySubst_admissible_subset (σ := σ) args a' (by grind)

          have : a'.freeVars ⊆ args.freeVars := by
            apply TermVector.freeVars_applySubst_admissible_subset (σ:= σ)
            . grind
            . grind
            . grind

          grind
        .
          simp at h₁
          rw[← h₁]
          simp[Term.freeVars]
          have := TermVector.freeVars_applySubst_admissible_subset
                    σ args a' (by rfl) (by grind) (by grind)
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
        have := Term.freeVars_applySubst_admissible_subset
                  σ t c (by grind) (by simp_all[Subst.admissible])

        have ih := Term.freeVars_applySubst_admissible_subset
              σ t c (by grind) (by simp_all[Subst.admissible])
        have : FCSet.univ.toSetᶜ = (∅ : Set Assignable) := by grind
        simp at ih
        grind
termination_by
  (σ.size, sizeOf t)
decreasing_by
  all_goals simp[Prod.lex_def]
  all_goals try omega
  .
    have := Subst.symbol_size σ s (by assumption)
    have := @TermVector.toSubst_size s.arity
    grind

end

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
              simp only [adjoint]

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
      next _ _ hg _ _ a _ =>
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
        have ih := Term.freeVars_applySubst_admissible_subset
              (σ := σ) t a (by grind) (by simp_all[Subst.admissible])
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
    have := Subst.symbol_size σ s (by assumption)
    have := @TermVector.toSubst_size s.arity
    grind

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
        have := Subst.preserve_semantics.term σ i v t₁
        have := Subst.preserve_semantics.term σ i v t₂
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
        sorry

theorem Subst.preserve_semantics.program
  (σ : Subst)
  (i : Interpretation)
  (v w : State)
  (α α' : Program)
  (hs : α' = Program.applySubst σ α)
  : ⟨v, w⟩ ∈ Program.denote i α' ↔ ⟨v, w⟩ ∈ Program.denote (Subst.adjoint σ i v) α := by
    match α with
      | .const a =>
        simp_all[Program.denote, Program.applySubst]
        grind
      | .assign x t =>
        simp_all[Program.denote, Program.applySubst, Option.bind]
        split at hs
        . contradiction
        rename Term => t'
        simp_all[Program.denote]
        have := Subst.preserve_semantics.term σ i v t t'
        grind
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
        sorry

end
