import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-725»

open scoped BigOperators

theorem centroid_pairwise_sqdist_identity
    {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hS : S.Nonempty) :
    let n : ℝ := (S.card : ℝ)
    let c : EuclideanSpace ℝ (Fin d) := (n⁻¹ : ℝ) • ∑ a ∈ S, a
    2 * n * (∑ a ∈ S, ‖a - c‖ ^ 2) = ∑ a ∈ S, ∑ a' ∈ S, ‖a - a'‖ ^ 2 := by
  sorry

end «CAM-Bench-725»
