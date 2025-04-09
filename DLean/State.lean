import DLean.Syntax

def State : Type := Assignable → ℝ

def State.update (s : State) (assignable : Assignable) (r : ℝ) : State := fun a =>
    if a = assignable then r
    else s a

def State.isEq (s₁ : State) (s₂ : State) : Prop :=
    ∀x:Assignable, s₁ x = s₂ x

def State.isEqExcept (s₁ : State) (s₂ : State) (except : List Assignable) :=
    ∀x:Assignable, ¬x ∈ except → s₁ x = s₂ x

lemma UpdatedStateIsIndeedUpdated (s : State) (a : Assignable) (r : ℝ) :
    s.update a r a = r := by
        dsimp [State.update]
        exact if_pos (by rfl)
