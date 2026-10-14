import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-435»

theorem S_is_convex
    (n : ℕ)
    (a : Fin n → ℝ)
    (hmono : StrictMono a)
    (α : ℝ) :
    Convex ℝ
      {p : Fin n → ℝ |
        (∑ i, p i = 1) ∧
        (∀ i, 0 ≤ p i) ∧
        (∑ i, p i * |a i| ^ 3 ≤ α * ∑ i, p i * |a i|)} := by
  sorry

end «CAM-Bench-435»
