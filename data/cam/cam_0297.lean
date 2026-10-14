import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-297»

theorem reciprocal_constraint_iff :
    ∀ {x y : ℝ},
      (1 / x + 1 / y ≤ 1 ∧ 0 < x ∧ 0 < y) ↔
        (1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ (x - 1) * (y - 1)) := by
  sorry

end «CAM-Bench-297»
