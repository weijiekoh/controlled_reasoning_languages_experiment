import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-421»

open scoped BigOperators

theorem convex_mem_sum_of_nonneg_eq_one
    {n k : ℕ} {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (x : Fin k → (Fin n → ℝ))
    (hx : ∀ i, x i ∈ C) (θ : Fin k → ℝ) (hθ : ∀ i, 0 ≤ θ i) (hsum : (∑ i, θ i) = 1) :
    (∑ i, θ i • x i) ∈ C := by
  sorry

end «CAM-Bench-421»
