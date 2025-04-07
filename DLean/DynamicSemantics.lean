import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import DLean.Syntax
import DLean.Interpretation
import DLean.State

noncomputable def Term.dynamicSemantics (i: Interpretation) (s : State) (t : Term) : ℝ :=
  match t with
    | Term.var  v         => s v
    | Term.neg  t         => - dynamicSemantics i s t
    | Term.plus x y       => dynamicSemantics i s x + dynamicSemantics i s y
    | Term.times x y      => dynamicSemantics i s x * dynamicSemantics i s y
    | Term.applyFn f args => let argValues := .map (fun ⟨e, h⟩ => dynamicSemantics i s e) args.toVector.attach
                             i f argValues
    | Term.differential t => let fvars := t.freeAssignables
                             List.sum $ fvars.map (
                              fun x =>
                                s (Assignable.diff x) *
                                (
                                  deriv (
                                    fun y => dynamicSemantics i (
                                      fun x' => if x = x' then y else s x'
                                    ) t
                                  ) (s x)
                                )
                             )
decreasing_by
  all_goals try decreasing_trivial
  have t : e ∈ args := (TermVector.mem_toVector_iff e args).mpr h
  have x : sizeOf e < sizeOf args := by
    apply TermVector.sizeOf_lt_of_mem t
  simp[*]
  omega
-- notation i s"〚"t"〛" => Term.dynamicSemantics i s t

def iterate (α : Program) (n : ℕ) := match n with
  | 0 => Program.test Formula.True
  | (n + 1) => Program.seq α $ iterate α n

def zip (xs : List ℕ) (ys : List ℕ) := match xs, ys with
  | .nil, .nil => List.nil
  | (x::xs), (y::ys) => (x + y) :: zip xs ys
  | (x::xs), .nil => x :: zip xs .nil
  | .nil, (y::ys) => y :: zip .nil ys

mutual
def Program.size (α : Program) : Ordinal := match α with
  | Program.assign _ _ => 1
  | Program.const _ => 1
  | Program.test Φ => Formula.size Φ + 1 -- todo formula size measure
  | Program.ode _ _ => 1
  | Program.choice α β  => α.size + β.size + 1 -- todo size
  | Program.seq α β  => α.size + β.size  + 1 -- todo size
  | Program.loop α =>  α.size * Ordinal.omega0 + 1

def Formula.size (Φ : Formula) : Ordinal := match Φ with
  | Formula.False => 1
  | Formula.True => 1
  | Formula.gte _ _ => 1
  | Formula.and Φ₁ Φ₂ => Φ₁.size + Φ₂.size + 1
  | Formula.not Φ₁ => Φ₁.size + 1
  | Formula.exists _ Φ => Φ.size + 1
  | Formula.forall _ Φ => Φ.size + 1
  | Formula.box α Φ => α.size + Φ.size + 1
  | Formula.diamond α Φ => α.size + Φ.size + 1
end

-- def size (xs : List ℕ) :=

mutual
def Formula.dynamicSemantics (i : Interpretation) (Φ : Formula) : Set State := match Φ with
  | Formula.True        => fun _ => true
  | Formula.False       => ∅
  | Formula.not Φ₁      => (Φ₁.dynamicSemantics i)ᶜ
  | Formula.and Φ₁ Φ₂   => (Φ₁.dynamicSemantics i) ∩ (Φ₂.dynamicSemantics i)
  | Formula.forall x Φ₁ => {s | ∀r:ℝ, (s.update (Assignable.var x) r) ∈ Φ₁.dynamicSemantics i}
  | Formula.exists x Φ₁ => {s | ∃r:ℝ, (s.update (Assignable.var x) r) ∈ Φ₁.dynamicSemantics i}
  | Formula.gte t₁ t₂   => {s | t₁.dynamicSemantics i s ≥ t₂.dynamicSemantics i s}
  | Formula.diamond α Φ => {s | ∃w:State, (s, w) ∈ α.dynamicSemantics i ∧ w ∈ Φ.dynamicSemantics i}
  | Formula.box α Φ     => {s | ∀w:State, (s, w) ∈ α.dynamicSemantics i → w ∈ Φ.dynamicSemantics i}
termination_by Φ.size
decreasing_by
  all_goals simp[Formula.size]
  exact Ordinal.le_add_left Φ₂.size Φ₁.size
  exact Ordinal.le_add_left Φ.size α.size
  exact Ordinal.le_add_left Φ.size α.size

  -- split
  -- all_goals try decreasing_trivial

  -- unfold Formula.size
  -- split
  -- all_goals try simp


-- notation i"〚"Φ"〛" => Formula.dynamicSemantics i Φ

def Program.dynamicSemantics (i : Interpretation) (α : Program) : Set (State × State) := match α with
  | Program.test Φ       => {(s, s) | s ∈ Φ.dynamicSemantics i}
  | Program.assign x t   => {(s₁, s₂) | s₂ = s₁.update x (t.dynamicSemantics i s₁)}
  | Program.choice α₁ α₂ => (α₁.dynamicSemantics i) ∪ (α₂.dynamicSemantics i)
  | Program.seq α₁ α₂    => {(s₁, s₂) | ∃v:State, (s₁, v) ∈ α₁.dynamicSemantics i ∧ (v, s₂) ∈ α₂.dynamicSemantics i}
  | Program.loop α       => {(s₁, s₂) | ∃n:ℕ, (s₁, s₂) ∈ Program.dynamicSemantics i (iterate α n)}
  | Program.ode _ _      => sorry
  | Program.const _      => sorry
termination_by α.size
decreasing_by
  all_goals simp[Program.size]
  exact Ordinal.le_add_left α₂.size α₁.size
  exact Ordinal.le_add_left α₂.size α₁.size

  unfold iterate
  split
  simp[Program.size]
  unfold Formula.size
  have hs : 0 < α.size := by
    unfold Program.size
    split
    all_goals simp
  have h : Ordinal.omega0 ≤ α.size * Ordinal.omega0 := by
    apply le_trans
    have x : Ordinal.omega0 ≤ 1 * Ordinal.omega0 := by simp +arith
    exact x
    refine mul_le_mul_right' ?_ Ordinal.omega0
    unfold Program.size
    split
    all_goals simp
    unfold Formula.size
    split
    all_goals exact (Order.one_le_iff_pos.mpr hs)

  have h2 : 1 < Ordinal.omega0 := Ordinal.one_lt_omega0
  apply lt_of_lt_of_le h2 h

  next n =>
  have ha : α.size + (iterate α n).size ≤ α.size * Nat.cast (4 * n + 3) := by
    induction n
    unfold iterate
    simp[Program.size]
    unfold Formula.size
    simp +arith
    have x : α.size ≥ 1 := by
      unfold Program.size
      split
      all_goals simp
      unfold Formula.size
      split
      all_goals exact Order.one_le_iff_pos.mpr (by simp +arith)
    sorry

    next h =>
    unfold iterate
    rw[Program.size]
    sorry

  simp[Program.size]

  apply lt_of_le_of_lt ha
  have hs : 0 < α.size := by
    unfold Program.size
    split
    all_goals simp
  apply (Ordinal.mul_lt_mul_iff_left hs).mpr
  apply Ordinal.nat_lt_omega0 (4*n + 3)

  -- simp +arith

  -- simp[Program.size]

  -- apply (Ordinal.mul_lt_mul_iff_left (sorry)).mpr


  -- have h : (iterate α n).size = n + 2 + α.size * n := by
    -- induction n
    -- simp
    -- unfold iterate
    -- unfold Program.size
    -- unfold Formula.size
    -- simp +arith

    -- next n h =>
    -- unfold iterate
    -- rw[Program.size]
    -- rw[h]







    -- have lol : α.size + α.size * ↑n + 2 < α.size * Order.succ ↑n + 2 := sorry
    -- apply lt_of_le_of_lt
    -- sorry
    -- exact lol

  -- apply le_trans
  -- exact h

  -- rw[h]

  -- have lulz : ↑n + 1 + α.size * ↑n ≤ α.size * ↑(n + n + 1) := sorry
  -- apply le_trans lulz
  -- apply (Ordinal.mul_le_mul_iff_left (sorry)).mpr
  -- apply le_of_lt
  -- apply?
  -- apply Ordinal.nat_lt_omega0 (n + n + 1)

end

#check Nat.add_le_mul
#check Ordinal.mul_le_mul_iff_left
