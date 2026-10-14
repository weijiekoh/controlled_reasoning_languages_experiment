import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-167»

def dualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ K, 0 ≤ ∑ i, y i * x i}

theorem dualCone_zero_eq_univ :
    dualCone ({0} : Set (Fin 2 → ℝ)) = Set.univ := by
  sorry

end «CAM-Bench-167»
