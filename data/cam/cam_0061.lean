import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-61»

theorem minimum_of_quadratic_on_feasible_set :
    (∀ x1 x2 : ℝ,
      x1 - x2 ≥ 0 →
      x1 + x2 ≤ 4 →
      x1 ≤ 3 →
      -1 ≤ 2 * x1 + 3 * x2 + 4 * x1 ^ 2 + 2 * x1 * x2 + x2 ^ 2) ∧
    ((0 : ℝ) - (-1 : ℝ) ≥ 0 ∧
      (0 : ℝ) + (-1 : ℝ) ≤ 4 ∧
      (0 : ℝ) ≤ 3 ∧
      (2 * (0 : ℝ) + 3 * (-1 : ℝ) + 4 * (0 : ℝ) ^ 2 + 2 * (0 : ℝ) * (-1 : ℝ) + (-1 : ℝ) ^ 2 = -1)) ∧
    (∀ x1 x2 : ℝ,
      x1 - x2 ≥ 0 →
      x1 + x2 ≤ 4 →
      x1 ≤ 3 →
      (2 * x1 + 3 * x2 + 4 * x1 ^ 2 + 2 * x1 * x2 + x2 ^ 2 = -1) ↔
        x1 = 0 ∧ x2 = -1) := by
  sorry

end «CAM-Bench-61»
