import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-11»

theorem transpose_mul_eq_zero_of_mul_transpose_mul_eq_zero
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (J : Matrix n m ℝ) (r : n → ℝ)
    (h : J.mulVec (J.transpose.mulVec r) = 0) :
    J.transpose.mulVec r = 0 := by
  sorry

end «CAM-Bench-11»
