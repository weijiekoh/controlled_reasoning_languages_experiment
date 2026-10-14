import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-691»

def IsChebyshevSet (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin n),
    ∃! p, p ∈ C ∧ ∀ c, c ∈ C → ‖z - p‖ ≤ ‖z - c‖

theorem projection_constant_on_segment_to_chebyshev_point
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsChebyshevSet C)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∉ C) :
    ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 →
      let p := Classical.choose (hC x₀)
      let x := θ • x₀ + (1 - θ) • p
      Classical.choose (hC x) = p := by
  sorry

end «CAM-Bench-691»
