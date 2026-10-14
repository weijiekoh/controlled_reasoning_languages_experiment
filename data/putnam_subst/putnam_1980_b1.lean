import Mathlib

open Real

noncomputable abbrev putnam_1980_b1_solution : Set ℝ := {c : ℝ | c ≥ 1 / 2}
/--
For which real numbers $c$ is $(e^x+e^{-x})/2 \leq e^{cx^2}$ for all real $x$?
-/
theorem putnam_1980_b1
(c : ℝ)
: (∀ x : ℝ, (exp x + exp (-x)) / 2 ≤ exp (c * x ^ 2)) ↔ c ∈ putnam_1980_b1_solution :=
sorry
