import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-2»

theorem full_column_rank_iff_transpose_mul_self_posDef
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (h : Fintype.card n ≤ Fintype.card m) (J : Matrix m n ℝ) :
    J.rank = Fintype.card n ↔
      Matrix.PosDef (J.transpose * J) := by
  sorry

end «CAM-Bench-2»
