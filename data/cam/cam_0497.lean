import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-497»

theorem x1_sq_div_x2_convex_quasiconvex_not_concave_not_quasiconcave :
    ConvexOn ℝ {p : ℝ × ℝ | 0 < p.2} (fun p : ℝ × ℝ => p.1 ^ 2 / p.2) ∧
      QuasiconvexOn ℝ {p : ℝ × ℝ | 0 < p.2} (fun p : ℝ × ℝ => p.1 ^ 2 / p.2) ∧
      ¬ ConcaveOn ℝ {p : ℝ × ℝ | 0 < p.2} (fun p : ℝ × ℝ => p.1 ^ 2 / p.2) ∧
      ¬ QuasiconcaveOn ℝ {p : ℝ × ℝ | 0 < p.2} (fun p : ℝ × ℝ => p.1 ^ 2 / p.2) := by
  sorry

end «CAM-Bench-497»
