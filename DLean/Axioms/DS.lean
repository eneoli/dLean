import DLean.Syntax.Basic
import DLean.Syntax.Theorems
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics
import DLean.Semantics.Coincidence
import DLean.Semantics.FreeVariables

import DLean.Embedding.Shallow

import Mathlib.Analysis.ODE.Gronwall

open Semantics
open Embedding

open Set in
theorem eq_add_mul_of_hasDerivWithinAt_const
    (f : ℝ → ℝ) (c r y : ℝ)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) r, HasDerivWithinAt f c (Set.Icc (0 : ℝ) r) t)
    (hy₀ : 0 ≤ y) (hyr : y ≤ r) :
    f y = f 0 + c * y := by
  let g := fun t : ℝ => f 0 + c * t;

  -- By hypothesis, $f$ is differentiable on $[0, r]$ with derivative $c$.
  have hf_diff : DifferentiableOn ℝ f (Icc 0 r) := by
    intros t ht
    apply HasDerivWithinAt.differentiableWithinAt
    apply hderiv
    assumption

  -- the value of the derivative of f is c in [0, r]
  have hf_diff_val : ∀ t ∈ Ico 0 r, derivWithin f (Icc 0 r) t = c := by
    intros t ht
    apply HasDerivWithinAt.derivWithin
    . grind
    .
      apply uniqueDiffOn_Icc
      . grind
      . grind

  -- $g$ is differentiable on $[0, r]$.
  have hg_diff : DifferentiableOn ℝ g (Icc 0 r) := by
    simp[g]
    apply DifferentiableOn.const_mul
    apply differentiableOn_id

 -- the value of the derivative of g is c in [0, r]
  have hg_diff_val : ∀ t ∈ Ico 0 r, derivWithin g (Icc 0 r) t = c := by
    intros t ht
    rw[derivWithin_const_add]
    rw[derivWithin_const_mul]
    .
      rw[derivWithin_id']
      . simp
      .
        apply uniqueDiffOn_Icc
        . grind
        . grind
    . apply differentiableWithinAt_id'

  -- $f$ and $g$ have the same derivative on $[0, r)$.
  have h_deriv_eq : ∀ t ∈ Set.Ico 0 r, derivWithin f (Set.Icc 0 r) t = derivWithin g (Set.Icc 0 r) t := by
    grind

  apply eq_of_derivWithin_eq
  . assumption
  . assumption
  . intros t ht ; grind
  . simp
  . grind

theorem fin_0_fn : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun _ : Fin 0 ↦ 0) := by
  intros
  funext x
  have := x.2
  grind

theorem DS : sound [Formula| (∀t, (t≥0 → (∀s, (0≤s ∧ s ≤ t → q(x + f() * s))) → [x := x + f()*t]p(x)))
                            → [x’ = f() & q(x)]p(x)] := by
  intros i s₁
  set x : Variable := .base "x"
  set x' : Variable := .diff x
  set f : FunctionSymbol := .udef "f" 0

  apply Formula.coincidence (v := s₁.update x' ((i (Symbol.Function f)).1 fun x ↦ 0)) (i := i) (j := i)
  .
    and_intros
    .
      simp_all[
        Formula.freeVars,
        Program.freeVars,
        OdeSystem.variables,
        Set.EqOn,
        Term.freeVars,
        Program.mustBoundVars,
        Program.boundVars,
        Variable.diff_emb,
        FunctionSymbol.arity,
        Formula.implies,
        Formula.or,
        Formula.lte,
      ]
      grind

    . simp

  simp[Formula.denote_implies]
  intros h₁



  simp[Formula.denote]

  intros s₂ h₂

  simp[Program.denote] at h₂
  obtain ⟨r, hr, φ, hp⟩ := h₂


  simp[Formula.denote] at h₁
  simp[Formula.denote_implies] at h₁

  conv at h₁ =>
    rhs ; rhs ; rhs ; simp[Formula.denote]


  simp[odeEvolutionFormula, Formula.denote, OdeSystem.variables, Variable.diff_emb] at hp

  set t : Variable := .base "t"
  have : Term.denote i s₂ (.var x) = Term.denote i (s₂.update t r) (.var x) := by
    simp[Term.denote]
    grind

  rw[this]

  apply h₁ (a := r)
  .
    simp[Formula.denote, Term.denote]
    grind
  .
    set s : Variable := .base "s"

    simp[Formula.denote_forall, Formula.denote_implies]
    intros y h₃

    simp[Formula.denote]

    simp[Formula.denote_leq, Formula.denote_and] at h₃
    simp[Term.denote] at h₃
    have ha := (hp.2.2 y (by grind) (by grind)).1.2
    have hb := (hp.2.2 y (by grind) (by grind)).1.1

    simp[Term.denote] at hb


    have : Term.denote i (φ y) (.var x)
         = Term.denote i ((s₁.update t r).update s y) [Term| x + f () * s] := by
      simp[Term.denote]
      have : (s₁.update t r).update s y s = y    := by rfl
      rw[this]
      have : (s₁.update t r).update s y x = s₁ x := by rfl
      rw[this]

      simp_all[FunctionSymbol.arity]

      have hfn : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun x : Fin 0 ↦ 0) := by
        intros
        funext x
        have := x.2
        grind

      rw[hfn]
      rw[hfn] at hb
      rw[← hb]

      have : s₁ x = φ 0 x := by
        simp[State.isEqExcept, Set.EqOn] at hp
        grind

      rw[this]

      apply eq_add_mul_of_hasDerivWithinAt_const (fun y ↦ φ y x) (y := y) (c := φ y x') (r := r)
      .
        intros t ht
        have := (hp.2.2 t (by grind) (by grind)).2.2

        have : (φ t x') = (φ y x') := by
          have hb' := (hp.2.2 t (by grind) (by grind)).1.1
          simp[Term.denote] at hb'
          simp_all[FunctionSymbol.arity]
          grind
        grind
      . grind
      . grind

    have : Term.denote i ((s₁.update t r).update s y) [Term| x + f () * s]
         = Term.denote i ((((s₁.update x' ((i (Symbol.Function f)).1 fun x ↦ 0))).update t r).update s y) [Term| x + f () * s] := by
         simp_all[Term.denote, State.update, Function.update]
         split
         .
          simp_all [FunctionSymbol.arity]
          have hfn : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun x : Fin 0 ↦ 0) := by
            intros
            funext x
            have := x.2
            grind
          simp[hfn]
         . grind

    grind
  .
    simp[Program.denote, Term.denote]

    rw[hp.2.1]

    have := hp.2.2 r (by grind) (by grind)

    funext y

    by_cases y = x'
    .
      simp_all[Term.denote]
      have := (hp.2.2 r (by grind) (by grind)).1.1
      rw[this]
      simp[FunctionSymbol.arity]

      have hfn : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun x : Fin 0 ↦ 0) := by
        intros
        funext x
        have := x.2
        grind
      rw[hfn]
    .
      by_cases y = x
      .
        simp_all[Term.denote]
        simp_all[FunctionSymbol.arity]
        have foo := ((hp.2.2 r) (by grind) (by grind)).1.1
        simp at foo

        rw[show (φ r).update t r x = φ r x by grind]

        have : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun x : Fin 0 ↦ 0) := by
          intros
          funext x
          have := x.2
          grind

        rw[this]
        rw[this] at foo
        rw[← foo]

        rw[show (s₁.update x' (φ r x')).update t r x = s₁ x by grind]
        rw[show s₁ x = φ 0 x by simp_all[State.isEqExcept, Set.EqOn] ; grind]
        rw[this]

        rw[← foo]

        apply eq_add_mul_of_hasDerivWithinAt_const (fun y ↦ φ y x) (y := r) (c := φ r x') (r := r)
        .
          intros t ht
          have hp' := (hp.2.2 t (by grind) (by grind)).2.2

          have : φ t x' = φ r x' := by
            have hb' := (hp.2.2 t (by grind) (by grind)).1.1
            have hb'' := (hp.2.2 r (by grind) (by grind)).1.1
            simp at hb'
            rw[hb']
            rw[hb'']
            simp_all
          grind
        . grind
        . grind
      .
        simp_all
        by_cases y = t
        . simp_all
        .
          simp_all[State.isEqExcept, Set.EqOn]
          grind

theorem DS₂ : sound [Formula| [x’ = f() & q(x)]p(x)
                            → (∀t, (t≥0 → (∀s, (0≤s ∧ s ≤ t → q(x + f() * s)))
                                    → [x := x + f()*t]p(x)))] := by
  intro i s

  let s₁ := s.update [Var|x’] ([Term|f()].denote i s)
  apply Formula.coincidence (v := s₁) (i := i)
  .
    simp[Formula.freeVars, Formula.implies, Formula.or, Program.freeVars, Program.mustBoundVars,
      Program.boundVars, Term.freeVars, TermVector.freeVars, Formula.lte, Variable.diff_emb,
      OdeSystem.variables]
    grind only [Set.EqOn, = Function.update.eq_1, = Set.mem_insert_iff, = Set.mem_diff,
      = Set.mem_singleton_iff]

  simpFormula
  simpTerm
  simp only [Function.update_self, CharP.cast_eq_zero, Rat.cast_zero, ge_iff_le, ne_eq,
    Variable.base.injEq, String.reduceEq, not_false_eq_true, Function.update_of_ne, and_imp]
  intro h r hr hq
  simp[Formula.denote, Program.denote_assign]
  simpTerm
  simp
  simp[Formula.denote, Program.denote, OdeSystem.variables, Variable.diff_emb, Term.denote] at h
  let φ := fun t ↦ s₁.update [Var|x] (s₁ [Var|x] + [Term|f()].denote i s₁ * t)
  specialize @h (φ r) r hr φ _ rfl
  . simp only [State.isEqExcept]
    grind only [Set.EqOn, = Function.update.eq_1, = Set.mem_compl_iff, = Set.mem_singleton_iff]
  have hf : ∀ s₁ s₂, [Term|f()].denote i s₂ = [Term|f()].denote i s₁ := by
      intro _ _
      apply Term.coincidence
      simp[Term.freeVars, TermVector.freeVars]

  suffices i (Symbol.Predicate {name:="p", arity:=1}) fun x ↦ φ r [Var|x] by
    specialize hf (s₁.update [Var|t] r)
    clear * - hf this
    simp_all only [Function.update_self, φ]

  apply h
  intro ζ hζ0 hζr
  and_intros
  . simp[odeEvolutionFormula]
    simpFormula
    simpTerm
    specialize hq ζ hζ0 hζr
    simp[φ, hf s, s₁]
    simp[Formula.denote, Term.denote_plus, Term.denote_times, Term.denote_var] at ⊢ hq
    simp[hf s] at hq
    assumption
  . grind only [State.isEqExcept, Set.EqOn, = Function.update.eq_1, = Set.mem_compl_iff,
    = Set.mem_insert_iff, = Set.mem_singleton_iff]
  . simp [hf s, φ, s₁]

    have := HasDerivWithinAt.const_mul ([Term|f()].denote i s) (hasDerivWithinAt_id ζ (Set.Icc 0 r))
    simp_all only [id_eq, mul_one]
