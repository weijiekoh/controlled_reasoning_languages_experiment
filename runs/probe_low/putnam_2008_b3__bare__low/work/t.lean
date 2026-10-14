import Mathlib
open Metric
abbrev E := EuclideanSpace ℝ (Fin 4)
lemma nsq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : inner ℝ u v = 0) (a b : ℝ) :
    ‖a • u + b • v‖^2 = a^2 + b^2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, h, hu, hv]
  simp [mul_pow, sq_abs]
