import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-170»

open scoped RealInnerProductSpace

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

theorem dualCone_eq_diagonal_subspace :
    dualCone {x : EuclideanSpace ℝ (Fin 2) | x 0 + x 1 = 0} =
      {y : EuclideanSpace ℝ (Fin 2) | ∃ t : ℝ, y = ![t, t]} := by
  sorry

end «CAM-Bench-170»
