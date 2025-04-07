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

inductive LoopClosure (sem : Set (State × State)) : State → State → Prop where
  | rfl   : (v : State) → LoopClosure sem v v
  | trans : (v : State)
            → (s : State)
            → (w : State)
            → LoopClosure sem v s
            → sem ⟨s, w⟩
            → LoopClosure sem v w

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

-- notation i"〚"Φ"〛" => Formula.dynamicSemantics i Φ

def Program.dynamicSemantics (i : Interpretation) (α : Program) : Set (State × State) := match α with
  | Program.test Φ       => {(s, s) | s ∈ Φ.dynamicSemantics i}
  | Program.assign x t   => {(s₁, s₂) | s₂ = s₁.update x (t.dynamicSemantics i s₁)}
  | Program.choice α₁ α₂ => (α₁.dynamicSemantics i) ∪ (α₂.dynamicSemantics i)
  | Program.seq α₁ α₂    => {(s₁, s₂) | ∃v:State, (s₁, v) ∈ α₁.dynamicSemantics i ∧ (v, s₂) ∈ α₂.dynamicSemantics i}
  | Program.loop α       => fun ⟨s₁, s₂⟩ => LoopClosure (α.dynamicSemantics i) s₁ s₂
  | Program.ode _ _      => sorry
  | Program.const _      => sorry

end

#check Bool
#check Prop

example (a: 1 = 2) (b : 1 = 2) : a = b := rfl
