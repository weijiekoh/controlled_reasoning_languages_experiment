import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-436»

theorem second_moment_sublevel_set_convex
    {n : ℕ} (a : Fin n → ℝ) (ha : StrictMono a) (α : ℝ) :
    Convex ℝ {p : Fin n → ℝ | (∑ i, p i) = 1 ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i * (a i)^2) ≤ α} := by
  sorry

end «CAM-Bench-436»
