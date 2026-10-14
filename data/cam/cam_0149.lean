import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-149»

theorem exist_distinct_quadratics_agree_on_six_points_of_circle
    (a b r : ℝ)
    (hr : 0 < r)
    (P : Fin 6 → ℝ × ℝ)
    (hP_on_circle : ∀ i : Fin 6, ((P i).1 - a) ^ 2 + ((P i).2 - b) ^ 2 = r ^ 2)
    (hP_distinct : Function.Injective P) :
    ∃ q₁ q₂ : ℝ × ℝ → ℝ,
      q₁ ≠ q₂ ∧
      (∃ α β γ δ ε ζ : ℝ,
        q₁ = fun p =>
          α * p.1 ^ 2 + β * p.1 * p.2 + γ * p.2 ^ 2 + δ * p.1 + ε * p.2 + ζ) ∧
      (∃ α β γ δ ε ζ : ℝ,
        q₂ = fun p =>
          α * p.1 ^ 2 + β * p.1 * p.2 + γ * p.2 ^ 2 + δ * p.1 + ε * p.2 + ζ) ∧
      ∀ i : Fin 6, q₁ (P i) = q₂ (P i) := by
  sorry

end «CAM-Bench-149»
