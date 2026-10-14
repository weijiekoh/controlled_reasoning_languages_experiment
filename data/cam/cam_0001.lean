import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-1»

theorem rank_eq_finrank_iff_transpose_mul_self_nonsingular
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (hmn : Fintype.card m ≥ Fintype.card n) (J : Matrix m n ℝ) :
    Module.finrank ℝ (LinearMap.range J.toLin') = Fintype.card n ↔
      IsUnit (Matrix.det (J.transpose * J)) := by
  sorry

end «CAM-Bench-1»
