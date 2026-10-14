import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-238»

def effectiveDomain {n : ℕ} (g : (Fin n → ℝ) → WithTop ℝ) : Set (Fin n → ℝ) :=
  {x | g x < ⊤}

theorem directionalInfQuotient_convex
    {n : ℕ}
    {g : (Fin n → ℝ) → WithTop ℝ}
    {y : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ}
    (hg : ∀ u v : Fin n → ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      g (θ • u + (1 - θ) • v) ≤ (θ : WithTop ℝ) * g u + ((1 - θ : ℝ) : WithTop ℝ) * g v)
    (hy : y ∈ effectiveDomain g)
    (hf : ∀ x : Fin n → ℝ,
      ((sInf
          {q : WithTop ℝ |
            ∃ α : ℝ, 0 < α ∧
              q = ((α⁻¹ : ℝ) : WithTop ℝ) * (g (y + α • x) - g y)} : WithTop ℝ) : WithTop ℝ) = (f x : WithTop ℝ)) :
    ConvexOn ℝ Set.univ f := by
  sorry

end «CAM-Bench-238»
