import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-470»

theorem copositive_dual_cone_eq_convex_hull_rankOne_nonneg :
    let C : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {X | X.IsSymm ∧ ∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) → 0 ≤ dotProduct z (X.mulVec z)}
    let dualC : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {Y | Y.IsSymm ∧ ∀ X ∈ C, 0 ≤ Matrix.trace (Y * X)}
    dualC =
      convexHull ℝ {Y | ∃ z : Fin n → ℝ, (∀ i, 0 ≤ z i) ∧ Y = Matrix.vecMulVec z z} := by
  sorry

end «CAM-Bench-470»
