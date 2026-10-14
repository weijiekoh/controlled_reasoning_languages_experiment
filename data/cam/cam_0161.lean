import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-161»

open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

theorem dualCone_of_nonnegative_preimage_eq_range_transpose_nonnegative
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    dualCone {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, 0 ≤ (A.mulVec x) i} =
      {y : EuclideanSpace ℝ (Fin n) |
        ∃ v : EuclideanSpace ℝ (Fin m), (∀ i : Fin m, 0 ≤ v i) ∧ y = Aᵀ.mulVec v} := by
  sorry

end «CAM-Bench-161»
