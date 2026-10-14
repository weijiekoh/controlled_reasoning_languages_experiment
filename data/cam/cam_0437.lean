import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-437»

open scoped BigOperators

theorem convex_probability_weights_with_large_second_moment
    {n : ℕ} (a : Fin n → ℝ) (α : ℝ) (ha : StrictMono a) :
    Convex ℝ
      {p : Fin n → ℝ |
        (∑ i, p i) = 1 ∧
        (∀ i, 0 ≤ p i) ∧
        α ≤ ∑ i, (a i)^2 * p i} := by
  sorry

end «CAM-Bench-437»
