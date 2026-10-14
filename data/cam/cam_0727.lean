import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-727»

open Matrix

theorem blockMatrix_psd_iff_sub_rankOne_psd {n : Type*} [Fintype n] [DecidableEq n]
    (x : n → ℝ) (X : Matrix n n ℝ) (hX : X.IsSymm) :
    (X - Matrix.vecMulVec x x).PosSemidef ↔
      (Matrix.fromBlocks X (fun i _ => x i) (fun _ j => x j)
        (1 : Matrix Unit Unit ℝ)).PosSemidef := by
  sorry

end «CAM-Bench-727»
