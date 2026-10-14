import Mathlib
example (a b : Matrix (Fin 1) (Fin 1) ℝ) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]
#check @Matrix.mul_apply
