import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-692»

def IsChebyshevSet (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin n),
    ∃! p, p ∈ C ∧ ∀ z, z ∈ C → ‖y - p‖ ≤ ‖y - z‖

theorem projection_eq_along_ray_of_chebyshev
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : IsChebyshevSet C)
    {x₀ x : EuclideanSpace ℝ (Fin n)}
    (hx₀_not_mem : x₀ ∉ C) :
    ∀ θ : ℝ, 1 ≤ θ →
      x = θ • x₀ + (1 - θ) • Classical.choose (ExistsUnique.exists (hC x₀)) →
      Classical.choose (ExistsUnique.exists (hC x)) = Classical.choose (ExistsUnique.exists (hC x₀)) := by
  sorry

end «CAM-Bench-692»
