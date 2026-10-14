import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-96»

def QQuadraticallyConvergent (x : ℕ → ℝ) (xStar : ℝ) : Prop :=
  Tendsto x atTop (𝓝 xStar) ∧
    ∃ M > 0, ∃ k0 : ℕ, ∀ k ≥ k0, |x (k + 1) - xStar| ≤ M * |x k - xStar| ^ 2

theorem qQuadraticallyConvergent_one_plus_half_pow_two_pow :
    QQuadraticallyConvergent (fun k : ℕ => 1 + (1 / 2 : ℝ) ^ (2 ^ k)) 1 := by
  sorry

end «CAM-Bench-96»
