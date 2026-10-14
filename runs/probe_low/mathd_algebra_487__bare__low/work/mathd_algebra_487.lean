import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1)
  (h₄ : a ≠ c) :
  Real.sqrt ((a - c)^2 + (b - d)^2)= Real.sqrt 10 := by
  subst h₀ h₂
  have h5 : (a - c) * (a + c + 1) = 0 := by nlinarith
  have h6 : a + c + 1 = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd (sub_eq_zero.mp h) h₄
    · exact h
  have hc : c = -1 - a := by linarith
  subst hc
  congr 1
  nlinarith