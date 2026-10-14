import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-465»

theorem dualCone_eq_nonneg_transpose_mul
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    {y : m → ℝ | ∀ z ∈ {z : m → ℝ | ∃ x : n → ℝ, (∀ i, 0 ≤ x i) ∧ z = A.mulVec x}, 0 ≤ y ⬝ᵥ z} =
      {y : m → ℝ | ∀ j, 0 ≤ (Aᵀ.mulVec y) j} := by
  sorry

end «CAM-Bench-465»
