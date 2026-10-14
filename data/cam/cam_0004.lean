import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-4»

def euclideanNorm {n : Type*} [Fintype n] (x : n → ℝ) : ℝ :=
  Real.sqrt (∑ i : n, x i ^ 2)

theorem orthogonal_matrix_preserves_euclidean_norm
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ)
    (hQ : Q.transpose * Q = 1)
    (x : n → ℝ) :
    euclideanNorm (Q.mulVec x) = euclideanNorm x := by
  sorry

end «CAM-Bench-4»
