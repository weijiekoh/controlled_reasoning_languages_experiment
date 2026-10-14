import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-462»

def IsConvexCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ K ∧
    (∀ ⦃x : Fin n → ℝ⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K)

def DualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  { y | ∀ ⦃x⦄, x ∈ K → 0 ≤ (∑ i, x i * y i) }

theorem dualCone_isConvexCone {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsConvexCone (n := n) K) :
    IsConvexCone (n := n) (DualCone (n := n) K) := by
  sorry

end «CAM-Bench-462»
