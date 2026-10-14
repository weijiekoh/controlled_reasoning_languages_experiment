import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  constructor <;>
  rcases abs_cases (x - 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases x with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rcases abs_cases (x + 1) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
  linarith