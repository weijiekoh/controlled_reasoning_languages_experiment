import Mathlib

open Set

noncomputable abbrev putnam_2006_b5_solution : ℝ := 1 / 16
/--
For each continuous function $f: [0,1] \to \mathbb{R}$, let $I(f) = \int_0^1 x^2 f(x)\,dx$ and $J(x) = \int_0^1 x \left(f(x)\right)^2\,dx$. Find the maximum value of $I(f) - J(f)$ over all such functions $f$.
-/
theorem putnam_2006_b5
  (I J : (ℝ → ℝ) → ℝ)
  (hI : I = fun f ↦ ∫ x in (0)..1, x ^ 2 * (f x))
  (hJ : J = fun f ↦ ∫ x in (0)..1, x * (f x) ^ 2) :
  IsGreatest
    {y | ∃ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) ∧ I f - J f = y}
    putnam_2006_b5_solution :=
by
  subst hI hJ
  constructor
  · refine ⟨fun x => x / 2, ?_, ?_⟩
    · exact (continuous_id.div_const 2).continuousOn
    · show (∫ x in (0)..1, x ^ 2 * (x / 2)) - (∫ x in (0)..1, x * (x / 2) ^ 2) = putnam_2006_b5_solution
      have h : (∫ x in (0:ℝ)..1, x ^ 2 * (x / 2)) - (∫ x in (0:ℝ)..1, x * (x / 2) ^ 2)
          = ∫ x in (0:ℝ)..1, x ^ 3 / 4 := by
        rw [← intervalIntegral.integral_sub]
        · congr 1; ext x; ring
        · exact (by fun_prop : Continuous fun x : ℝ => x ^ 2 * (x / 2)).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun x : ℝ => x * (x / 2) ^ 2).intervalIntegrable _ _
      rw [h]
      simp [integral_pow]
      norm_num [putnam_2006_b5_solution]
  · rintro y ⟨f, hf, rfl⟩
    show (∫ x in (0)..1, x ^ 2 * (f x)) - (∫ x in (0)..1, x * (f x) ^ 2) ≤ putnam_2006_b5_solution
    have hc : ContinuousOn (fun x => x ^ 2 * f x) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact (continuousOn_id.pow 2).mul hf
    have hd : ContinuousOn (fun x => x * (f x) ^ 2) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact continuousOn_id.mul (hf.pow 2)
    have hle : (∫ x in (0)..1, x ^ 2 * (f x)) - (∫ x in (0)..1, x * (f x) ^ 2)
        ≤ ∫ x in (0:ℝ)..1, x ^ 3 / 4 := by
      rw [← intervalIntegral.integral_sub (hc.intervalIntegrable) (hd.intervalIntegrable)]
      apply intervalIntegral.integral_mono_on zero_le_one
      · exact (hc.sub hd).intervalIntegrable
      · exact (by fun_prop : Continuous fun x : ℝ => x ^ 3 / 4).intervalIntegrable _ _
      · intro x hx
        have hx0 : 0 ≤ x := hx.1
        have hfx : f x = f x := rfl
        have key := mul_nonneg hx0 (sq_nonneg (f x - x / 2))
        show x ^ 2 * f x - x * f x ^ 2 ≤ x ^ 3 / 4
        nlinarith [key]
    have hval : (∫ x in (0:ℝ)..1, x ^ 3 / 4) = putnam_2006_b5_solution := by
      simp [integral_pow, putnam_2006_b5_solution]
      norm_num
    rw [hval] at hle
    exact hle
