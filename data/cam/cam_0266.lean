import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-266»

theorem perspective_nonincreasing_in_t
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (h0 : f 0 ≤ 0) :
    ∀ ⦃x : Fin n → ℝ⦄ ⦃t₁ t₂ : ℝ⦄,
      0 < t₁ → t₁ ≤ t₂ → t₁ * f (fun i => x i / t₁) ≥ t₂ * f (fun i => x i / t₂) := by
  sorry

end «CAM-Bench-266»
