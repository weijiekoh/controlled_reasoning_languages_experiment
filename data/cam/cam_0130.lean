import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-130»

open Matrix

theorem bfgs_inverse_update_is_inverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (sk yk : n → ℝ) (Bk Hk : Matrix n n ℝ)
    (hBk_inv : IsUnit Bk.det)
    (hHk : Hk = Bk⁻¹)
    (hskBkSk : (dotProduct sk (Bk *ᵥ sk)) ≠ 0)
    (hykTsk : (dotProduct yk sk) ≠ 0) :
    let ρk : ℝ := (dotProduct yk sk)⁻¹
    let Bk1 : Matrix n n ℝ :=
      Bk
        - ((dotProduct sk (Bk *ᵥ sk))⁻¹ : ℝ) • ((Bk * Matrix.vecMulVec sk sk) * Bk)
        + ((dotProduct yk sk)⁻¹ : ℝ) • Matrix.vecMulVec yk yk
    let Hk1 : Matrix n n ℝ :=
      (((1 : Matrix n n ℝ) - ρk • Matrix.vecMulVec sk yk) * Hk *
        ((1 : Matrix n n ℝ) - ρk • Matrix.vecMulVec yk sk))
        + ρk • Matrix.vecMulVec sk sk
    Hk1 = Bk1⁻¹ := by
  sorry

end «CAM-Bench-130»
