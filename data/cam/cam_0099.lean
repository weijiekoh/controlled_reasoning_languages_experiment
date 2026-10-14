import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-99»

def IsSaddlePoint {n : ℕ} (f : (Fin n → ℝ) → ℝ) (xStar : Fin n → ℝ) : Prop :=
  ¬ IsLocalMin f xStar ∧
  ¬ IsLocalMax f xStar ∧
  ∀ ε : ℝ, 0 < ε →
    ∃ x y : Fin n → ℝ,
      x ∈ Metric.ball xStar ε ∧ y ∈ Metric.ball xStar ε ∧ f x < f xStar ∧ f xStar < f y

theorem exists_unique_stationary_point_and_is_saddle_for_quadratic :
    ∃! xStar : Fin 2 → ℝ,
      ((2 : ℝ) * xStar 0 + 8 = 0 ∧ (-4 : ℝ) * xStar 1 + 12 = 0) ∧
      IsSaddlePoint
        (fun x : Fin 2 → ℝ => 8 * x 0 + 12 * x 1 + (x 0) ^ 2 - 2 * (x 1) ^ 2)
        xStar := by
  sorry

end «CAM-Bench-99»
