import Mathlib
open Polynomial IntermediateField

theorem cplx : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ aeval (a : ℂ) (X ^ 4 - X ^ 2 - 1 : ℚ[X]) = 0 ∧
    aeval ((b : ℂ) * Complex.I) (X ^ 4 - X ^ 2 - 1 : ℚ[X]) = 0 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : 1 < Real.sqrt 5 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have A : ∀ x : ℝ, x ^ 2 = (1 + Real.sqrt 5) / 2 → x ^ 4 - x ^ 2 - 1 = 0 := by
    intro x hx
    have : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [this, hx]; nlinarith
  have B : ∀ x : ℝ, x ^ 2 = (Real.sqrt 5 - 1) / 2 → x ^ 4 + x ^ 2 - 1 = 0 := by
    intro x hx
    have : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [this, hx]; nlinarith
  refine ⟨Real.sqrt ((1 + Real.sqrt 5) / 2), Real.sqrt ((Real.sqrt 5 - 1) / 2), ?_, ?_, ?_, ?_⟩
  · apply Real.sqrt_pos.mpr; linarith
  · apply Real.sqrt_pos.mpr; linarith
  · have ha : Real.sqrt ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 := Real.sq_sqrt (by linarith)
    simp only [map_sub, map_pow, aeval_X, map_one]
    exact_mod_cast A _ ha
  · have hb : Real.sqrt ((Real.sqrt 5 - 1) / 2) ^ 2 = (Real.sqrt 5 - 1) / 2 := Real.sq_sqrt (by linarith)
    simp only [map_sub, map_pow, aeval_X, map_one]
    have := B _ hb
    generalize Real.sqrt ((Real.sqrt 5 - 1) / 2) = y at this
    have h2 : ((y : ℂ) * Complex.I) ^ 4 - ((y : ℂ) * Complex.I) ^ 2 - 1
        = ((y ^ 4 + y ^ 2 - 1 : ℝ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_pow, Complex.I_pow_four, Complex.I_sq]; ring
    rw [h2, this]; simp
