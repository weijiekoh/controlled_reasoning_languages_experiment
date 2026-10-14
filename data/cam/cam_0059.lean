import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-59»

theorem maximum_of_quadratic_on_simplex_region :
    IsGreatest
      {r : ℝ |
        ∃ x1 x2 : ℝ,
          x1 + x2 ≤ 3 ∧
          0 ≤ x1 ∧
          0 ≤ x2 ∧
          r = 6 * x1 + 4 * x2 - 13 - x1^2 - x2^2}
      (-2) ∧
    ((2 : ℝ), (1 : ℝ)).1 + ((2 : ℝ), (1 : ℝ)).2 ≤ 3 ∧
    0 ≤ ((2 : ℝ), (1 : ℝ)).1 ∧
    0 ≤ ((2 : ℝ), (1 : ℝ)).2 ∧
    6 * ((2 : ℝ), (1 : ℝ)).1 + 4 * ((2 : ℝ), (1 : ℝ)).2 - 13
      - ((2 : ℝ), (1 : ℝ)).1^2 - ((2 : ℝ), (1 : ℝ)).2^2 = -2 ∧
    ∀ p : ℝ × ℝ,
      p.1 + p.2 ≤ 3 →
      0 ≤ p.1 →
      0 ≤ p.2 →
      6 * p.1 + 4 * p.2 - 13 - p.1^2 - p.2^2 = -2 →
      p = (2, 1) := by
  sorry

end «CAM-Bench-59»
