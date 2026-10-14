import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-570»

open scoped Topology

theorem gaussian_tail_integral_bound
    {x : ℝ}
    (hquad : ∀ ⦃t : ℝ⦄, t ≤ x → t ^ 2 - x ^ 2 ≥ 2 * x * (t - x)) :
    (∀ ⦃t : ℝ⦄, t ≤ x → Real.exp (-(t ^ 2) / 2) ≤ Real.exp (x ^ 2 / 2) * Real.exp (-x * t)) ∧
    ((∫ t in Set.Iic x, Real.exp (-(t ^ 2) / 2)) ≤
      Real.exp (x ^ 2 / 2) * (∫ t in Set.Iic x, Real.exp (-x * t))) := by
  sorry

end «CAM-Bench-570»
