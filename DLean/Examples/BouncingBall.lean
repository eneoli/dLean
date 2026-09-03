import DLean.Syntax.Syntax
import DLean.Embedding.Embedding

open Embedding

theorem bouncing_ball : ⌈0.0 ≤ x ∧ x = H ∧ v = 0 ∧ g > 0 ∧ 1 ≥ c ∧ c ≥ 0 →
                                [(x’ = v, v’ = -g & x ≥ 0 ; (?x = 0; v := -c*v ∪ ?x ≠ 0))*] (0 ≤ x ∧ x ≤ H)⌉
  := by
  sorry
