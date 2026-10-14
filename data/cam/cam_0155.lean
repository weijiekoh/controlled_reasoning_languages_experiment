import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-155»

theorem convex_iff_add_smul_eq_smul_add
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    Convex ℝ C ↔
      ∀ ⦃α β : ℝ⦄, 0 ≤ α → 0 ≤ β →
        Set.image (fun x => (α + β) • x) C =
          {z | ∃ x ∈ C, ∃ y ∈ C, α • x + β • y = z} := by
  sorry

end «CAM-Bench-155»
