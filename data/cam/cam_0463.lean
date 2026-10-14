import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-463»

def dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { y | ∀ x, x ∈ K → 0 ≤ Finset.univ.sum (fun i : Fin n => x i * y i) }

theorem dualCone_anti_monotone {n : ℕ}
    {K₁ K₂ : Set (EuclideanSpace ℝ (Fin n))}
    (hK₁_convex : Convex ℝ K₁)
    (hK₁_cone : ∀ ⦃a : ℝ⦄ ⦃x : EuclideanSpace ℝ (Fin n)⦄, 0 ≤ a → x ∈ K₁ → a • x ∈ K₁)
    (hK₂_convex : Convex ℝ K₂)
    (hK₂_cone : ∀ ⦃a : ℝ⦄ ⦃x : EuclideanSpace ℝ (Fin n)⦄, 0 ≤ a → x ∈ K₂ → a • x ∈ K₂)
    (hsubset : K₁ ⊆ K₂) :
    dualCone K₂ ⊆ dualCone K₁ := by
  sorry

end «CAM-Bench-463»
