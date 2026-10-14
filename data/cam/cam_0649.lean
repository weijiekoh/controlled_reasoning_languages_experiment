import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-649»

def dualCone (K : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ y ∈ K, 0 ≤ Complex.re (dotProduct (fun i => star (x i)) y)}

open scoped RealInnerProductSpace

theorem dualCone_KPR_characterization
    {n : ℕ} (z : Fin n → ℂ)
    (hz_distinct : Function.Injective z)
    (hz_outside : ∀ i, 1 < ‖z i‖) :
    dualCone
      {y | ∃ f : ℂ → ℂ,
        AnalyticOn ℂ f {w : ℂ | 1 < ‖w‖} ∧
        (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ Complex.re (f w)) ∧
        ∀ k : Fin n, y k = f (z k)} =
      {x | Complex.re (∑ l : Fin n, x l) = 0 ∧
        ∀ θ : ℝ,
          θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) →
            0 ≤
              Complex.re
                (∑ l : Fin n,
                  x l *
                    ((Complex.exp (-θ * Complex.I) + (star (z l))⁻¹) /
                      (Complex.exp (-θ * Complex.I) - (star (z l))⁻¹))) } := by
  sorry

end «CAM-Bench-649»
