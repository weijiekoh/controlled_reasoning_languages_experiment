import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-453»

theorem supporting_hyperplane_closedUnitBall_iff
    {n : ℕ} (xhat s : Fin n → ℝ) (hs : s ≠ 0)
    (hxhat_boundary : (∀ i, |xhat i| ≤ 1) ∧ ∃ i, |xhat i| = 1) :
    (((∀ x : Fin n → ℝ, (∀ i, |x i| ≤ 1) → ∑ i, s i * x i ≥ ∑ i, s i * xhat i) ∧
      (∃ x : Fin n → ℝ,
        (∀ i, |x i| ≤ 1) ∧
        (∑ i, s i * x i = ∑ i, s i * xhat i))) ↔
    ((∀ i, xhat i = 1 → s i ≤ 0) ∧
      (∀ i, xhat i = -1 → s i ≥ 0) ∧
      (∀ i, -1 < xhat i ∧ xhat i < 1 → s i = 0))) := by
  sorry

end «CAM-Bench-453»
