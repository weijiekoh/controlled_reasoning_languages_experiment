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
    putnam_2006_b5_solution := by
  subst hI hJ
  constructor
  · refine ⟨fun x => x / 2, (continuous_id.div_const 2).continuousOn, ?_⟩
    have h1 : ∫ x in (0:ℝ)..1, x ^ 2 * (x / 2) = ∫ x in (0:ℝ)..1, x ^ 3 / 2 := by
      congr 1; funext x; ring
    have h2 : ∫ x in (0:ℝ)..1, x * (x / 2) ^ 2 = ∫ x in (0:ℝ)..1, x ^ 3 / 4 := by
      congr 1; funext x; ring
    show (∫ x in (0:ℝ)..1, x ^ 2 * (x / 2)) - (∫ x in (0:ℝ)..1, x * (x / 2) ^ 2) = 1 / 16
    rw [h1, h2, intervalIntegral.integral_div, intervalIntegral.integral_div]
    norm_num [integral_pow]
  · rintro y ⟨f, hf, rfl⟩
    show (∫ x in (0:ℝ)..1, x ^ 2 * f x) - (∫ x in (0:ℝ)..1, x * f x ^ 2) ≤ 1 / 16
    have hfc : ContinuousOn f (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]; exact hf
    have hi1 : IntervalIntegrable (fun x => x ^ 2 * f x) MeasureTheory.volume 0 1 :=
      (ContinuousOn.mul (by fun_prop) hfc).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x => x * f x ^ 2) MeasureTheory.volume 0 1 :=
      (ContinuousOn.mul (by fun_prop) (hfc.pow 2)).intervalIntegrable
    have hi3 : IntervalIntegrable (fun x : ℝ => x ^ 3 / 4) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have key : ∫ x in (0:ℝ)..1, (x ^ 2 * f x - x * f x ^ 2) ≤ ∫ x in (0:ℝ)..1, x ^ 3 / 4 := by
      apply intervalIntegral.integral_mono_on zero_le_one (hi1.sub hi2) hi3
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      nlinarith [mul_nonneg hx0 (sq_nonneg (f x - x / 2))]
    have hval : ∫ x in (0:ℝ)..1, x ^ 3 / 4 = 1 / 16 := by
      rw [intervalIntegral.integral_div]; norm_num [integral_pow]
    have hs := intervalIntegral.integral_sub hi1 hi2
    linarith
