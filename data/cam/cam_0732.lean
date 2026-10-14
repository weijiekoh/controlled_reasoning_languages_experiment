import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-732»

theorem trace_inner_eq_zero_iff_mul_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (X S : Matrix n n ℝ)
    (hXsymm : X.IsSymm) (hSsymm : S.IsSymm)
    (hXpsd : X.PosSemidef) (hSpsd : S.PosSemidef) :
    Matrix.trace (X * S) = 0 ↔ X * S = 0 := by
  sorry

end «CAM-Bench-732»
