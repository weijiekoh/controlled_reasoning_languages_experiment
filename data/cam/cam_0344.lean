import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-344»

theorem exp_integral_on_nonnegative_orthant_finite_iff
    (n : ℕ) (θ : Fin n → ℝ) :

    ((MeasureTheory.IntegrableOn
        (fun x : Fin n → ℝ => Real.exp (∑ i, θ i * x i))
        {x | ∀ i, 0 ≤ x i}) ↔ (∀ i, θ i < 0)) ∧

    ((∀ i, θ i < 0) →
      ∫ x : Fin n → ℝ in {x | ∀ i, 0 ≤ x i},
        Real.exp (∑ i, θ i * x i) = ∏ i : Fin n, (-θ i)⁻¹) := by
  sorry

end «CAM-Bench-344»
