import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-105»

theorem argminSet_convex
    {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hD : Convex ℝ D)
    (hf : ConvexOn ℝ D f) :
    Convex ℝ {x | x ∈ D ∧ ∀ y ∈ D, f x ≤ f y} := by
  sorry

end «CAM-Bench-105»
