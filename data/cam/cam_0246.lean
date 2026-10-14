import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-246»

theorem convex_iff_three_point_determinant_nonneg (f : ℝ → ℝ) :
    ConvexOn ℝ Set.univ f ↔
      ∀ ⦃x y z : ℝ⦄, x < y → y < z →
        0 ≤ Matrix.det ![![1, 1, 1], ![x, y, z], ![f x, f y, f z]] := by
  sorry

end «CAM-Bench-246»
