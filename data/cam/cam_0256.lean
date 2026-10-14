import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-256»

theorem weighted_geometric_mean_concaveOn
    {n : ℕ} (θ : Fin n → ℝ)
    (hθ_nonneg : ∀ i, 0 ≤ θ i)
    (hθ_sum : ∑ i, θ i ≤ 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => ∏ i, (x i) ^ (θ i)) := by
  sorry

end «CAM-Bench-256»
