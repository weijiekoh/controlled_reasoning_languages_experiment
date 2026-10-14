import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-296»

theorem fourth_power_constraint_iff_exists_square_bound (x y : ℝ) :
    (x + y) ^ 4 ≤ x - y ↔ ∃ t : ℝ, t ≥ (x + y) ^ 2 ∧ t ^ 2 ≤ x - y := by
  sorry

end «CAM-Bench-296»
