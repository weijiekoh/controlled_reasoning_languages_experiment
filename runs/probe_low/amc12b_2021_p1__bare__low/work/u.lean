import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12b_2021_p1
  (S : Finset ℤ)
  (h₀ : ∀ (x : ℤ), x ∈ S ↔ ↑(abs x) < 3 * Real.pi):
  S.card = 19 := by
  have h1 := Real.pi_gt_three
  have h2 := Real.pi_lt_d2
  have : S = Finset.Icc (-9) 9 := by
    ext x
    rw [h₀, Finset.mem_Icc]
    constructor
    · intro h
      have : ((|x| : ℤ) : ℝ) < 10 := by linarith
      have : |x| < 10 := by exact_mod_cast this
      rw [abs_lt] at this
      omega
    · intro h
      have : |x| ≤ 9 := abs_le.mpr ⟨by omega, by omega⟩
      have : ((|x| : ℤ) : ℝ) ≤ 9 := by exact_mod_cast this
      linarith
  rw [this]; rfl
