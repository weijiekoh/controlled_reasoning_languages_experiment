import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-103»

def IsIsolatedLocalMinimizer {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsLocalMin f xStar ∧
    ∃ r : ℝ,
      0 < r ∧
        ∀ x : EuclideanSpace ℝ (Fin n),
          ‖x - xStar‖ < r → IsLocalMin f x → x = xStar

theorem isolatedLocalMinimizer_has_strictly_smaller_value_nearby
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {xStar : EuclideanSpace ℝ (Fin n)}
    (hx : IsIsolatedLocalMinimizer f xStar) :
    ∃ r : ℝ,
      0 < r ∧
        ∀ x : EuclideanSpace ℝ (Fin n),
          0 < ‖x - xStar‖ ∧ ‖x - xStar‖ < r → f xStar < f x := by
  sorry

end «CAM-Bench-103»
