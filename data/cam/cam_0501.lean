import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-501»

theorem weighted_sorted_sum_convexOn
    (n : ℕ) (α : Fin n → ℝ)
    (hα_mono : Antitone α)
    (hα_nonneg : ∀ i : Fin n, 0 ≤ α i) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        sSup {r : ℝ | ∃ σ : Equiv.Perm (Fin n), r = ∑ i : Fin n, α i * x (σ i)}) := by
  sorry

end «CAM-Bench-501»
