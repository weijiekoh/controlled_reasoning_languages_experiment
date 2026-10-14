import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-259»

open scoped BigOperators

theorem weighted_geom_monomial_convex_of_one_pos_exponent
    {n : ℕ} (θ : Fin n → ℝ)
    (hsum : 1 ≤ ∑ i, θ i)
    (hunique : ∃! k : Fin n, 0 < θ k ∧ ∀ i, i ≠ k → θ i ≤ 0) :
    ConvexOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i} (fun x => ∏ i, (x i) ^ (θ i)) := by
  sorry

end «CAM-Bench-259»
