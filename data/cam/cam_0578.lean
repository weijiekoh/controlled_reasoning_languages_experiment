import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-578»

theorem convex_bounded_above_on_univ_is_constant
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (M : ℝ) (hM : ∀ x : Fin n → ℝ, f x ≤ M) :
    ∃ c : ℝ, ∀ x : Fin n → ℝ, f x = c := by
  sorry

end «CAM-Bench-578»
