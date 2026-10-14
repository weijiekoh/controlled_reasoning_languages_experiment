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
  have hpow : (∫ x in (0:ℝ)..1, x^3/4) = 1/16 := by
    rw [intervalIntegral.integral_div, integral_pow]; norm_num
  constructor
  · refine ⟨fun x => x/2, (continuous_id.div_const 2).continuousOn, ?_⟩
    show (∫ x in (0:ℝ)..1, x^2*(x/2)) - (∫ x in (0:ℝ)..1, x*(x/2)^2) = 1/16
    have e1 : ∀ x:ℝ, x^2*(x/2) - x*(x/2)^2 = x^3/4 := fun x => by ring
    rw [← intervalIntegral.integral_sub, ← hpow]
    · congr 1
      ext x
      exact e1 x
    · exact (by fun_prop : Continuous fun x:ℝ => x^2*(x/2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x:ℝ => x*(x/2)^2).intervalIntegrable _ _
  · rintro y ⟨f, hf, rfl⟩
    show (∫ x in (0:ℝ)..1, x^2*(f x)) - (∫ x in (0:ℝ)..1, x*(f x)^2) ≤ 1/16
    have hc : ContinuousOn f (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]; exact hf
    have i1 : IntervalIntegrable (fun x:ℝ => x^2*(f x)) MeasureTheory.volume 0 1 :=
      ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop) hc)
    have i2 : IntervalIntegrable (fun x:ℝ => x*(f x)^2) MeasureTheory.volume 0 1 :=
      ContinuousOn.intervalIntegrable (ContinuousOn.mul (by fun_prop) (hc.pow 2))
    have i3 : IntervalIntegrable (fun x:ℝ => x^3/4 - x*(f x - x/2)^2) MeasureTheory.volume 0 1 :=
      ContinuousOn.intervalIntegrable (ContinuousOn.sub (by fun_prop)
        (ContinuousOn.mul (by fun_prop) ((hc.sub (by fun_prop)).pow 2)))
    have i4 : IntervalIntegrable (fun x:ℝ => x^3/4) MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous fun x:ℝ => x^3/4).intervalIntegrable _ _
    have heq : (∫ x in (0:ℝ)..1, x^2*(f x)) - (∫ x in (0:ℝ)..1, x*(f x)^2)
        = ∫ x in (0:ℝ)..1, (x^3/4 - x*(f x - x/2)^2) := by
      rw [← intervalIntegral.integral_sub i1 i2]
      congr 1
      ext x
      ring
    rw [heq, ← hpow]
    apply intervalIntegral.integral_mono_on zero_le_one i3 i4
    intro x hx
    have : 0 ≤ x * (f x - x/2)^2 := mul_nonneg hx.1 (sq_nonneg _)
    linarith
