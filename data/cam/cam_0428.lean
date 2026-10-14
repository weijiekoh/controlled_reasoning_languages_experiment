import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-428»

theorem box_set_convex {n : ℕ} (α β : Fin n → ℝ) :
    Convex ℝ {x : Fin n → ℝ | ∀ i, α i ≤ x i ∧ x i ≤ β i} := by
  sorry

end «CAM-Bench-428»
