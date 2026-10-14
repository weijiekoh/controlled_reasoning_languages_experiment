import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-434»

theorem exceedance_probability_set_convex
    {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) (α β : ℝ) :
    Convex ℝ
      {p : Fin n → ℝ |
        (∑ i, p i) = 1 ∧
        (∀ i, 0 ≤ p i) ∧
        (∑ i ∈ Finset.univ.filter (fun i => α < a i), p i) ≤ β} := by
  sorry

end «CAM-Bench-434»
