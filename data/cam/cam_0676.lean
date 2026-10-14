import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-676»

def StrictlyConvexNorm (n : ℕ) : Prop :=
  ∀ ⦃u v : EuclideanSpace ℝ (Fin n)⦄, u ≠ v →
    ∀ ⦃t : ℝ⦄, 0 < t → t < 1 →
      ‖t • u + (1 - t) • v‖ < t * ‖u‖ + (1 - t) * ‖v‖

theorem exists_unique_nearest_point_in_closed_convex_set
    (n : ℕ)
    (hstrict : StrictlyConvexNorm n)
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    ∀ x₀ : EuclideanSpace ℝ (Fin n),
      ∃! x : C, ∀ y : C, ‖x₀ - (x : EuclideanSpace ℝ (Fin n))‖ ≤ ‖x₀ - (y : EuclideanSpace ℝ (Fin n))‖ := by
  sorry

end «CAM-Bench-676»
