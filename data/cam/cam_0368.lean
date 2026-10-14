import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-368»

open scoped RealInnerProductSpace

theorem robust_separation_constraints_iff
    {n : ℕ} {C₁ C₂ : Set (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)} {b t : ℝ}
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty) :
    ((∀ x : EuclideanSpace ℝ (Fin n),
        (sInf {r : ℝ | ∃ y ∈ C₁, ‖x - y‖ ≤ r}) ≤ t → ⟪a, x⟫ + b ≥ 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        (sInf {r : ℝ | ∃ y ∈ C₂, ‖x - y‖ ≤ r}) ≤ t → ⟪a, x⟫ + b ≤ -1)) ↔
    ((∀ y ∈ C₁, ⟪a, y⟫ + b + t * ‖a‖ ≥ 1) ∧
      (∀ y ∈ C₂, ⟪a, y⟫ + b - t * ‖a‖ ≤ -1)) := by
  sorry

end «CAM-Bench-368»
