import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-264»

open scoped BigOperators

theorem negLog_t_sub_inv_mul_sq_norm_convexOn
    (n : ℕ)
    (hconv :
      ConvexOn ℝ
        {p : (Fin n → ℝ) × ℝ | ‖p.1‖ < p.2}
        (fun p : (Fin n → ℝ) × ℝ => -Real.log (p.2 ^ 2 - ‖p.1‖ ^ 2))) :
    ConvexOn ℝ
      {p : (Fin n → ℝ) × ℝ | ‖p.1‖ < p.2}
      (fun p : (Fin n → ℝ) × ℝ => -Real.log (p.2 - (‖p.1‖ ^ 2) / p.2)) := by
  sorry

end «CAM-Bench-264»
