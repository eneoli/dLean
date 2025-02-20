import DLean.Syntax

def State : Type := Assignable → ℝ

def updateState (s : State) (assignable : Assignable) (r : ℝ) : State :=
    fun a =>
        if a = assignable then
            r
        else
            s a

-- Lemmas

lemma UpdatedStateIsIndeedUpdated (s : State) (a : Assignable) (r : ℝ) :
    updateState s a r a = r := by
        dsimp [updateState]
        exact if_pos (by rfl)
