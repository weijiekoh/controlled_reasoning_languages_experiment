import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p1
  (S : Finset ℤ)
  (h₀ : ∀ (x : ℤ), x ∈ S ↔ ↑(abs x) < 3 * Real.pi):
  S.card = 19 := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have : S = Finset.Icc (-9) 9 := by
    ext x
    rw [h₀, Finset.mem_Icc]
    constructor
    · intro h
      have h3 : ((|x| : ℤ) : ℝ) < 10 := by linarith
      have h4 : |x| < 10 := by exact_mod_cast h3
      constructor <;> cases abs_cases x <;> omega
    · intro h
      have h3 : |x| ≤ 9 := by rw [abs_le]; omega
      have h4 : ((|x| : ℤ) : ℝ) ≤ 9 := by exact_mod_cast h3
      linarith
  rw [this]; rfl