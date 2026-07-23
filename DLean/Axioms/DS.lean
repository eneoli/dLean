import DLean.Syntax.Syntax
import DLean.Syntax.Theorems
import DLean.Semantics.State
import DLean.Semantics.Interpretation
import DLean.Semantics.DynamicSemantics
import DLean.Semantics.Coincidence
import DLean.Semantics.FreeVariables

import DLean.Embedding.Shallow

import DLean.Axioms.Base

import Mathlib.Analysis.ODE.Gronwall

open Semantics
open Embedding

open Set in
theorem eq_add_mul_of_hasDerivWithinAt_const
    (f : ℝ → ℝ) (c r y : ℝ)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) r,
      HasDerivWithinAt f c (Set.Icc (0 : ℝ) r) t)
    (hy₀ : 0 ≤ y) (hyr : y ≤ r) :
    f y = f 0 + c * y := by
  let g := fun t : ℝ => f 0 + c * t;
  -- By hypothesis, $f$ is differentiable on $[0, r]$ with derivative $c$.
  have hf_diff : DifferentiableOn ℝ f (Icc 0 r) := by
    exact fun t ht => ( hderiv t ht |> HasDerivWithinAt.differentiableWithinAt );
  -- By hypothesis, $g$ is differentiable on $[0, r]$ with derivative $c$.
  have hg_diff : DifferentiableOn ℝ g (Icc 0 r) := by
    fun_prop;
  -- By hypothesis, $f$ and $g$ have the same derivative on $[0, r)$.
  have h_deriv_eq : ∀ t ∈ Set.Ico 0 r, derivWithin f (Set.Icc 0 r) t = derivWithin g (Set.Icc 0 r) t := by
    intro t ht; have := hderiv t ⟨ ht.1, ht.2.le ⟩ ; have := this.derivWithin ( uniqueDiffOn_Icc ( by linarith [ ht.1, ht.2 ] ) t ⟨ ht.1, ht.2.le ⟩ ) ; simp_all +decide [ mul_comm c ] ;
    rw [ derivWithin_const_add, derivWithin_const_mul, derivWithin_id' ];
    · ring;
    · exact uniqueDiffOn_Icc ( by linarith ) t ⟨ by linarith, by linarith ⟩;
    · exact differentiableWithinAt_id;
  convert eq_of_derivWithin_eq hf_diff hg_diff h_deriv_eq _ y ⟨ hy₀, hyr ⟩;
  simp [g]

#check [Formula| (∀t, (t≥0 → (∀s, (0≤s ∧ s ≤ t → q(x + f() * s))) → [x := x + f()*t]p(x)))
               → [x’ = f() & q(x)]p(x)]

theorem fin_0_fn : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun x : Fin 0 ↦ 0) := by
  intros
  funext x
  have := x.2
  grind

theorem DS₁ : sound [Formula| (∀t, (t≥0 → (∀s, (0≤s ∧ s ≤ t → q(x + f() * s))) → [x := x + f()*t]p(x)))
                            → [x’ = f() & q(x)]p(x)] := by
  intros i s₁
  set x : Assignable := .var ⟨"x"⟩
  set x' : Assignable := .diff x
  set f : FunctionSymbol := .udef "f" 0



  -- this feels illegal
  apply Formula.coincidence (v := s₁.update x' ((i (Symbol.Function f)).1 fun x ↦ 0)) (i := i) (j := i)
  .
    and_intros
    .
      simp_all[
        Formula.freeVars,
        Program.freeVars,
        OdeSystem.assignables,
        Set.EqOn,
        Term.freeVars,
        Program.mustBoundVars,
        Program.boundVars,
        Assignable.diff_emb,
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


  simp[odeEvolutionFormula, Formula.denote, OdeSystem.assignables, Assignable.diff_emb] at hp

  set t : Assignable := .var ⟨"t"⟩
  have : Term.denote i s₂ (.var x) = Term.denote i (s₂.update t r) (.var x) := by
    simp[Term.denote]
    grind

  rw[this]

  apply h₁ (a := r)
  .
    simp[Formula.denote, Term.denote]
    grind
  .
    set s : Assignable := .var ⟨"s"⟩

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
          simp_all[Function.update, FunctionSymbol.arity]
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

    -- set x : Assignable := .var ⟨"x"⟩
    -- set x' : Assignable := .diff x
    -- set t : Assignable := .var ⟨"t"⟩

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
        simp[FunctionSymbol.arity] at foo

        rw[show (φ r).update t r x = φ r x by grind]
        -- rw[show s₁.update t r x = s₁ x by grind]

        have : ∀ t : Fin 0 → ℝ, (fun x : Fin 0 ↦ t x) = (fun x : Fin 0 ↦ 0) := by
          intros
          funext x
          have := x.2
          grind

        rw[this]
        rw[this] at foo
        rw[← foo]

        -- have : ((s₁).update t r) x = φ 0 x := by simp_all[State.isEqExcept, Set.EqOn]
        -- rw[this]
        rw[show (s₁.update x' (φ r x')).update t r x = s₁ x by grind]
        rw[show s₁ x = φ 0 x by simp_all[State.isEqExcept, Set.EqOn] ; grind]
        rw[this]

        rw[← foo]

        -- TODO code duplication
        apply eq_add_mul_of_hasDerivWithinAt_const (fun y ↦ φ y x) (y := r) (c := φ r x') (r := r)
        .
          intros t ht
          have hp' := (hp.2.2 t (by grind) (by grind)).2.2

          have : φ t x' = φ r x' := by
            have hb' := (hp.2.2 t (by grind) (by grind)).1.1
            have hb'' := (hp.2.2 r (by grind) (by grind)).1.1
            simp[Term.denote] at hb'
            rw[hb']
            rw[hb'']
            simp_all[FunctionSymbol.arity]
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
                            → (∀t, (t≥0 → (∀s, (0≤s ∧ s ≤ t → q(x + f() * s))) → [x := x + f()*t]p(x)))] := by
  intros i s₁

  set f  : FunctionSymbol := .udef "f" 0
  set x  : Assignable := .var ⟨"x"⟩
  set s  : Assignable := .var ⟨"s"⟩
  set t  : Assignable := .var ⟨"t"⟩
  set x' : Assignable := .diff x


  -- apply Formula.coincidence (i := i) (j := i) (v := s₁.update x' ((i (Symbol.Function f)).1 fun x ↦ 0))
  -- .
  --   simp_all[
  --     Set.EqOn,
  --     Formula.freeVars,
  --     Program.freeVars,
  --     Formula.implies,
  --     Formula.lte,
  --     Formula.gte,
  --     Formula.or,
  --     Term.freeVars,
  --     Program.mustBoundVars,
  --     Program.boundVars,
  --     OdeSystem.assignables,
  --     Assignable.diff_emb,
  --     FunctionSymbol.arity,
  --   ]
  --   grind

  simp[Formula.denote_implies]
  intros h₁

  simp[Formula.denote_forall]

  intros r
  simp[Formula.denote_implies]

  intros h₂ h₃

  simp[Formula.denote, Term.denote] at h₂

  simp[Formula.denote]

  intros s₂ h₄

  simp[Formula.denote] at h₁

  apply h₁

  simp[Program.denote]
  apply Exists.intro r
  and_intros
  . grind
  .
    simp[OdeSystem.assignables, Assignable.diff_emb]


    set φ : ℝ → State :=
      fun ζ ↦ fun y ↦
        if y = x then Term.denote i (s₁.update t ζ) [Term| x + f() * t]
        else if y = x' then (i f).1 (fun _ ↦ 0)
        else s₁ y

    apply Exists.intro φ
    and_intros
    .
      simp[State.isEqExcept, Set.EqOn, φ]
      intros y
      split
      .
        simp_all[Term.denote]
        grind
      . grind
    .
      funext z
      simp[φ]
      split
      .
        simp_all
        simp[Program.denote] at h₄
        rw[h₄]
        rfl
      .
        split
        .
          simp_all

          sorry
        .
          have hb := Program.bound_effect h₄
          simp_all[State.isEqExcept, Program.boundVars, Set.EqOn]
          have := @hb z (by grind)
          by_cases z = t
          .
            simp_all


            sorry
          . grind
    .
      intros ζ hl hr
      and_intros
      .
        simp[odeEvolutionFormula]
        simp[Formula.denote]
        and_intros
        .
          conv =>
            lhs ; simp[Term.denote, φ]

          split
          .
            simp[Term.denote, FunctionSymbol.arity, fin_0_fn]
            rfl
          . contradiction
        .
          simp[Term.denote, φ]
          simp[Formula.denote] at h₃

          specialize h₃ ζ
          simp[Formula.denote_implies] at h₃
          simp[Formula.denote_and, Formula.denote_leq, Term.denote] at h₃
          rw[show (s₁.update t r).update s ζ t = r by rfl] at h₃
          rw[show (s₁.update t r).update s ζ s = ζ by rfl] at h₃
          specialize h₃ (by grind) (by grind)
          simp[Formula.denote, Term.denote_plus, Term.denote_times, Term.denote] at h₃
          rw[show (s₁.update t r).update s ζ x = s₁ x by rfl] at h₃
          rw[show s₁.update t ζ t = ζ by rfl]
          rw[show s₁.update t ζ x = s₁ x by rfl]

          simp_all[FunctionSymbol.arity, fin_0_fn]
          grind
      .
        simp[φ, State.isEqExcept, Set.EqOn]
        grind
      . sorry
