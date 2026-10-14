import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-9»

open Matrix

def euclideanNorm {n : Type*} [Fintype n] (x : n → ℝ) : ℝ :=
  Real.sqrt (∑ i : n, x i ^ 2)

theorem phi_monotone_decreasing_unless_transpose_mul_vec_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℝ) (r : n → ℝ)
    (hInv : ∀ lam : ℝ, 0 ≤ lam →
      IsUnit (Jᵀ * J + lam • (1 : Matrix n n ℝ))) :
    Jᵀ.mulVec r ≠ 0 →
      StrictAntiOn
        (fun lam : ℝ =>
          euclideanNorm (((Jᵀ * J + lam • (1 : Matrix n n ℝ))⁻¹).mulVec (Jᵀ.mulVec r)))
        (Set.Ici 0) := by
  sorry

end «CAM-Bench-9»
