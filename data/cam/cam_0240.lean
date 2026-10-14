import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-240»

theorem orthogonal_sq_entries_doubly_stochastic_and_diag_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q Y : Matrix n n ℝ) (lam : n → ℝ)
    (horth_left : Q.transpose * Q = 1) (horth_right : Q * Q.transpose = 1)
    (hY : Y = Q * Matrix.diagonal lam * Q.transpose) :
    let S : Matrix n n ℝ := fun i j => Q i j ^ 2
    (∀ i j, 0 ≤ S i j) ∧
      (∀ i, ∑ j, S i j = 1) ∧
      (∀ j, ∑ i, S i j = 1) ∧
      Matrix.diag Y = S.mulVec lam := by
  sorry

end «CAM-Bench-240»
