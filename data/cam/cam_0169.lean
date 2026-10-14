import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-169»

open scoped RealInnerProductSpace

def dualCone {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ C, 0 ≤ ⟪y, x⟫}

theorem dualCone_eq_abs_le_in_R2 :
    dualCone {x : EuclideanSpace ℝ (Fin 2) | |x 0| ≤ x 1} =
      {y : EuclideanSpace ℝ (Fin 2) | |y 0| ≤ y 1} := by
  sorry

end «CAM-Bench-169»
