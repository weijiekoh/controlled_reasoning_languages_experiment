import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-560»

def LogConcaveOn (D : Set ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ D, 0 < f x) ∧
  ∀ ⦃x y : ℝ⦄, x ∈ D → y ∈ D →
    ∀ ⦃θ : ℝ⦄, θ ∈ Set.Icc (0 : ℝ) 1 →
      θ * x + (1 - θ) * y ∈ D →
      Real.log (f (θ * x + (1 - θ) * y)) ≥
        θ * Real.log (f x) + (1 - θ) * Real.log (f y)

theorem harmonic_mean_denominator_reciprocal_logConcaveOn
    (n : ℕ) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x : Fin n → ℝ => Real.log ((∑ i : Fin n, (x i)⁻¹)⁻¹)) := by
  sorry

end «CAM-Bench-560»
