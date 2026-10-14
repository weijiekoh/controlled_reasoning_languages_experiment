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
  have hu : uIcc (0:ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  constructor
  · refine ⟨fun x => x / 2, ?_, ?_⟩
    · exact (continuous_id.div_const 2).continuousOn
    · show (∫ x in (0:ℝ)..1, x ^ 2 * (x / 2)) - (∫ x in (0:ℝ)..1, x * (x / 2) ^ 2) = 1 / 16
      rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      have h1 : (fun x : ℝ => x ^ 2 * (x / 2) - x * (x / 2) ^ 2) = fun x => x ^ 3 / 4 := by
        funext x; ring
      simp only [h1]
      rw [intervalIntegral.integral_div, integral_pow]
      norm_num
  · rintro y ⟨f, hf, rfl⟩
    have i1 : IntervalIntegrable (fun x => x ^ 2 * f x) MeasureTheory.volume 0 1 :=
      ContinuousOn.intervalIntegrable (by
        rw [hu]; exact (continuousOn_id.pow 2).mul hf)
    have i2 : IntervalIntegrable (fun x => x * (f x) ^ 2) MeasureTheory.volume 0 1 :=
      ContinuousOn.intervalIntegrable (by
        rw [hu]; exact continuousOn_id.mul (hf.pow 2))
    have i3 : IntervalIntegrable (fun x : ℝ => x ^ 3 / 4) MeasureTheory.volume 0 1 :=
      ((continuous_id.pow 3).div_const 4).intervalIntegrable _ _
    show (∫ x in (0:ℝ)..1, x ^ 2 * f x) - (∫ x in (0:ℝ)..1, x * (f x) ^ 2) ≤ 1 / 16
    rw [← intervalIntegral.integral_sub i1 i2]
    have hm : (∫ x in (0:ℝ)..1, x ^ 2 * f x - x * (f x) ^ 2) ≤ ∫ x in (0:ℝ)..1, x ^ 3 / 4 :=
      intervalIntegral.integral_mono_on zero_le_one (i1.sub i2) i3 (by
        intro x hx
        have hx0 : 0 ≤ x := hx.1
        have : 0 ≤ x * (f x - x / 2) ^ 2 := mul_nonneg hx0 (sq_nonneg _)
        nlinarith [this])
    have hc : (∫ x in (0:ℝ)..1, x ^ 3 / 4) = 1 / 16 := by
      rw [intervalIntegral.integral_div, integral_pow]; norm_num
    show _ ≤ (1:ℝ) / 16
    linarith
