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
  have e1 : a*x^3+b*y^3 = (x+y)*(a*x^2+b*y^2) - x*y*(a*x+b*y) := by ring
  have e2 : a*x^4+b*y^4 = (x+y)*(a*x^3+b*y^3) - x*y*(a*x^2+b*y^2) := by ring
  have e3 : a*x^5+b*y^5 = (x+y)*(a*x^4+b*y^4) - x*y*(a*x^3+b*y^3) := by ring
  rw [h₀, h₁, h₂] at *
  rw [h₁, h₂] at e1
  rw [h₂, h₃] at e2
  rw [h₃, h₂] at e3
  have hp : x+y = -14 := by linarith
  have hq : x*y = -38 := by linarith
  rw [hp, hq] at e3
  linarith