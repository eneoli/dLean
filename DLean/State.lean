import DLean.Syntax

def State : Type := Assignable → ℝ

def State.update (s : State) (assignable : Assignable) (r : ℝ) : State := fun a =>
    if a = assignable then r
    else s a


lemma UpdatedStateIsIndeedUpdated (s : State) (a : Assignable) (r : ℝ) :
    s.update a r a = r := by
        dsimp [State.update]
        exact if_pos (by rfl)
