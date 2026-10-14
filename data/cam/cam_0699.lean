import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-699»

open scoped Matrix

theorem ellipsoids_disjoint_iff_exists_separating_vector
    (n : ℕ) (x₁ x₂ : Fin n → ℝ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ)
    (hP₁_symm : P₁.IsSymm) (hP₂_symm : P₂.IsSymm)
    (hP₁_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₁.mulVec v))
    (hP₂_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₂.mulVec v))
    (P₁sqrt P₂sqrt : Matrix (Fin n) (Fin n) ℝ)
    (hP₁sqrt_sq : P₁sqrt * P₁sqrt = P₁) (hP₂sqrt_sq : P₂sqrt * P₂sqrt = P₂)
    (hP₁sqrt_symm : P₁sqrt.IsSymm) (hP₂sqrt_symm : P₂sqrt.IsSymm)
    (hP₁sqrt_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₁sqrt.mulVec v))
    (hP₂sqrt_pos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (P₂sqrt.mulVec v)) :
    ({x : Fin n → ℝ |
        dotProduct (x - x₁) (P₁⁻¹.mulVec (x - x₁)) ≤ 1} ∩
      {x : Fin n → ℝ |
        dotProduct (x - x₂) (P₂⁻¹.mulVec (x - x₂)) ≤ 1} = (∅ : Set (Fin n → ℝ))) ↔
      ∃ a : Fin n → ℝ,
        ‖P₂sqrt.mulVec a‖ + ‖P₁sqrt.mulVec a‖ < dotProduct a (x₁ - x₂) := by
  sorry

end «CAM-Bench-699»
