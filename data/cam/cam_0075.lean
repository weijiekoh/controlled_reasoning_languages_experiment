import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-75»

theorem minSquare_has_second_derivative_at_zero_and_second_derivative_not_continuous :
    (∃ a : ℝ, HasDerivAt (fun z : ℝ => deriv (fun y : ℝ => (min 0 y) ^ 2) z) a 0) ∧
    ¬ ContinuousAt (fun z : ℝ => deriv (fun y : ℝ => deriv (fun w : ℝ => (min 0 w) ^ 2) y) z) 0 := by
  sorry

end «CAM-Bench-75»
