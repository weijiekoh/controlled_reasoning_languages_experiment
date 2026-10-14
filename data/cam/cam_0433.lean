import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-433»

theorem eroded_set_convex
    {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (a : ℝ)
    (ha : 0 ≤ a) (hS : Convex ℝ S) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin n) | Metric.closedBall x a ⊆ S} := by
  sorry

end «CAM-Bench-433»
