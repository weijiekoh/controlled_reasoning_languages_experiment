import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-718»

open scoped Matrix BigOperators

theorem constrained_quadratic_sublevel_affine_eq_convex
    {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b g : n → ℝ) (c h lam : ℝ)
    (hpsd : Matrix.PosSemidef (A + lam • (Matrix.vecMulVec g g))) :
    Convex ℝ {x : n → ℝ | x ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ x + c ≤ 0 ∧ g ⬝ᵥ x + h = 0} := by
  sorry

end «CAM-Bench-718»
