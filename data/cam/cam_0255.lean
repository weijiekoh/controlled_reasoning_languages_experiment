import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-255»

open scoped BigOperators

theorem weighted_geometric_mean_concave
    (n : ℕ) (θ : Fin n → ℝ)
    (hθ_nonneg : ∀ i, 0 ≤ θ i)
    (hθ_sum : ∑ i, θ i = 1) :
    ConcaveOn ℝ {z : Fin n → ℝ | ∀ i, 0 < z i}
      (fun z => ∏ i, Real.rpow (z i) (θ i)) := by
  sorry

end «CAM-Bench-255»
