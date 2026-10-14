import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-254»

theorem weighted_geometric_mean_concave_on_pos
    (theta : ℝ × ℝ) (hθ1 : 0 ≤ theta.1) (hθ2 : 0 ≤ theta.2) (hθsum : theta.1 + theta.2 = 1) :
    ConcaveOn ℝ {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2}
      (fun x : ℝ × ℝ => x.1 ^ theta.1 * x.2 ^ theta.2) := by
  sorry

end «CAM-Bench-254»
