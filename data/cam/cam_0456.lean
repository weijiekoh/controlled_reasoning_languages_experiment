import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-456»

open scoped BigOperators

def IsSupportingHyperplane (C : Set (Fin n → ℝ)) (x a : Fin n → ℝ) (b : ℝ) : Prop :=
  a ≠ 0 ∧ x ∈ C ∧ (∑ i, a i * x i) = b ∧ ∀ y, y ∈ C → (∑ i, a i * y i) ≤ b

theorem convex_of_supportingHyperplane_at_boundary
    (C : Set (Fin n → ℝ))
    (hC_closed : IsClosed C)
    (hC_interior_nonempty : (interior C).Nonempty)
    (h_support :
      ∀ x, x ∈ frontier C →
        ∃ a b, IsSupportingHyperplane (n := n) C x a b) :
    Convex ℝ C := by
  sorry

end «CAM-Bench-456»
