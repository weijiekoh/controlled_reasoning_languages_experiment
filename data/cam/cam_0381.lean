import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-381»

theorem abs_dot_le_twoNorm_mul_twoNorm {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := by
  sorry

end «CAM-Bench-381»
