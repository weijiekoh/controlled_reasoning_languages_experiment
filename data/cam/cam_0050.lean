import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-50»

open Matrix

theorem block_column_matrices_linearIndependent
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m m ℝ) (N : Matrix m n ℝ) (hB : Invertible B) :
    LinearIndependent ℝ
      (fun j : Sum m n =>
        fun i : Sum m n =>
          (Matrix.fromBlocks (⅟ B) (-(⅟ B * N)) 0 1 : Matrix (Sum m n) (Sum m n) ℝ) i j) := by
  sorry

end «CAM-Bench-50»
