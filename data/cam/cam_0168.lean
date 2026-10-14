import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-168»

def dualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ K, 0 ≤ ∑ i, y i * x i}

theorem dualCone_eq_singleton_zero_of_univ :
    dualCone (n := 2) (Set.univ : Set (Fin 2 → ℝ)) = ({0} : Set (Fin 2 → ℝ)) := by
  sorry

end «CAM-Bench-168»
