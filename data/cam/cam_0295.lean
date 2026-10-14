import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-295»

theorem euclideanNorm_pair_eq_zero_iff :
    ∀ x y : ℝ,
      ‖![x + 2 * y, x - y]‖ = 0 ↔ x + 2 * y = 0 ∧ x - y = 0 := by
  sorry

end «CAM-Bench-295»
