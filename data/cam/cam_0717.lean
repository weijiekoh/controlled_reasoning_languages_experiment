import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-717»

theorem sublevelSet_quadraticForm_convex
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (hA_symm : A.IsSymm) (hA_pos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ A.mulVec x) :
    Convex ℝ {x : n → ℝ | x ⬝ᵥ A.mulVec x + b ⬝ᵥ x + c ≤ 0} := by
  sorry

end «CAM-Bench-717»
