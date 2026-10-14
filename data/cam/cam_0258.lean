import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-258»

open scoped BigOperators

theorem weighted_geometric_monomial_convex_of_unique_positive_exponent
    {n : ℕ} (θ : Fin n → ℝ)
    (hsum : ∑ i, θ i = 1)
    (hunique : ∃! k : Fin n, 0 < θ k ∧ ∀ j : Fin n, j ≠ k → θ j ≤ 0) :
    ConvexOn ℝ {z : Fin n → ℝ | ∀ i : Fin n, 0 < z i}
      (fun z => ∏ i, Real.rpow (z i) (θ i)) := by
  sorry

end «CAM-Bench-258»
