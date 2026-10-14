import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-517»

theorem interval_indicator_sum_is_convex_concave_quasiconvex_quasiconcave
    (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i j : Fin n, i < j → a i < a j) (α β : ℝ) :
    let Δ : Set (Fin n → ℝ) :=
      {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}
    let f : (Fin n → ℝ) → ℝ :=
      fun p => ∑ i : Fin n, if α ≤ a i ∧ a i ≤ β then p i else 0
    ConvexOn ℝ Δ f ∧ ConcaveOn ℝ Δ f ∧
      (∀ r : ℝ, Convex ℝ {p | p ∈ Δ ∧ f p ≤ r}) ∧
      (∀ r : ℝ, Convex ℝ {p | p ∈ Δ ∧ r ≤ f p}) := by
  sorry

end «CAM-Bench-517»
