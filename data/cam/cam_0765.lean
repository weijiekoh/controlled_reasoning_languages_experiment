import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-765»

theorem positiveSemidefinite_iff_quadraticForm_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) :
    A.PosSemidef ↔ ∀ x : n → ℝ, 0 ≤ dotProduct x (A.mulVec x) := by
  sorry

end «CAM-Bench-765»
