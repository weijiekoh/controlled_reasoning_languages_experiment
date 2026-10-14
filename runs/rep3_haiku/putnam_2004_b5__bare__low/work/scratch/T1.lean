import Mathlib
open Nat Topology Filter

lemma term_bound (x a : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (ha : 0 < a) (ha1 : a ≤ 1) :
    -((1 - x) * (a - a * x)) ≤ a * (Real.log (1 + a * x) - Real.log (1 + a))
      + (a - a * x) - (Real.log (1 + a) - Real.log (1 + a * x)) ∧
    a * (Real.log (1 + a * x) - Real.log (1 + a))
      + (a - a * x) - (Real.log (1 + a) - Real.log (1 + a * x)) ≤ 0 := by
  have hax : 0 < a * x := mul_pos ha hx0
  have hax' : a * x < a := by nlinarith
  have hp0 : 0 < 1 + a * x := by linarith
  have hq0 : 0 < 1 + a := by linarith
  have hpq : 1 + a * x < 1 + a := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
  rw [Real.log_div hp0.ne' hq0.ne'] at h1
  rw [Real.log_div hq0.ne' hp0.ne'] at h2
  have e1 : (1 + a) * ((1 + a * x) / (1 + a) - 1) = (1 + a * x) - (1 + a) := by
    field_simp
  have e2 : (1 + a * x) * ((1 + a) / (1 + a * x) - 1) = (1 + a) - (1 + a * x) := by
    field_simp
  have m1 := mul_le_mul_of_nonneg_left h1 hq0.le
  have m2 := mul_le_mul_of_nonneg_left h2 hp0.le
  set L := Real.log (1 + a) - Real.log (1 + a * x) with hL
  have hA : (1 + a) * L ≥ a - a * x := by nlinarith
  have hB : (1 + a * x) * L ≤ a - a * x := by nlinarith
  have hX : (a - a * x) - (1 + a) * L ≥ -(a - a*x)^2 := by
    nlinarith [mul_nonneg hq0.le hp0.le]
  have hE : (a - a*x)^2 ≤ (a - a*x) * (1 - x) := by
    have : a * (1 - x) ≤ 1 - x := by nlinarith
    nlinarith
  have expr : a * (Real.log (1 + a * x) - Real.log (1 + a))
      + (a - a * x) - (Real.log (1 + a) - Real.log (1 + a * x)) = (a - a*x) - (1 + a) * L := by
    rw [hL]; ring
  rw [expr]
  constructor
  · nlinarith
  · linarith
