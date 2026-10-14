import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 := by
  have e1 : 16 = (x+y)*7 - (x*y)*3 := by rw [← h₂, ← h₁, ← h₀]; ring
  have e2 : 42 = (x+y)*16 - (x*y)*7 := by rw [← h₃, ← h₂, ← h₁]; ring
  have hp : x+y = -14 := by linarith
  have hq : x*y = -38 := by linarith
  have e3 : a * x^5 + b * y^5 = (x+y)*(a * x^4 + b * y^4) - (x*y)*(a * x^3 + b * y^3) := by ring
  rw [e3, h₃, h₂, hp, hq]; norm_num