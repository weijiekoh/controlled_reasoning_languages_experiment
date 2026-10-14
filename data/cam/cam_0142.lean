import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-142»

theorem hessian_adjacency_subgraph_intersection_graph
    {n : ℕ} {H : Fin n → Fin n → ℝ}
    (hdiag : ∀ i : Fin n, H i i ≠ 0) :
    ∀ ⦃i j : Fin n⦄, i ≠ j → H i j ≠ 0 → ∃ k : Fin n, H k i ≠ 0 ∧ H k j ≠ 0 := by
  sorry

end «CAM-Bench-142»
