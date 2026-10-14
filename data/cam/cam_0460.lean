import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-460»

open scoped Pointwise

theorem closed_midpoint_convex {n : ℕ} {C : Set (Fin n → ℝ)}
    (hclosed : IsClosed C)
    (hmid : ∀ ⦃a b⦄, a ∈ C → b ∈ C → ( (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b ) ∈ C) :
    Convex ℝ C := by
  sorry

end «CAM-Bench-460»
