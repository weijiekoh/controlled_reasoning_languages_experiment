import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-5»

def HasQRColumnPivoting {m n : ℕ} (J : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ (π : Equiv.Perm (Fin n)) (Q : Matrix (Fin m) (Fin m) ℝ) (R : Matrix (Fin n) (Fin n) ℝ),
    Matrix.of (fun i j => J i (π j)) =
      Q * Matrix.of (fun i j => if h : i.1 < n then R ⟨i.1, h⟩ j else 0) ∧
    Q * Q.transpose = 1 ∧
    Q.transpose * Q = 1 ∧
    R.BlockTriangular id

theorem choleskyFactor_eq_R_of_qrColumnPivoting_id
    {m n : ℕ}
    (J : Matrix (Fin m) (Fin n) ℝ)
    (hfull : Function.Injective fun x : Fin n → ℝ => J.mulVec x)
    (Rbar R : Matrix (Fin n) (Fin n) ℝ)
    (hRbar_tri : Rbar.BlockTriangular id)
    (hRbar_pos : ∀ i : Fin n, 0 < Rbar i i)
    (hgram : J.transpose * J = Rbar.transpose * Rbar)
    (hqr :
      ∃ (Q : Matrix (Fin m) (Fin m) ℝ),
        Matrix.of (fun i j => J i ((Equiv.refl (Fin n)) j)) =
          Q * Matrix.of (fun i j => if h : i.1 < n then R ⟨i.1, h⟩ j else 0) ∧
        Q * Q.transpose = 1 ∧
        Q.transpose * Q = 1 ∧
        R.BlockTriangular id)
    (hR_pos : ∀ i : Fin n, 0 < R i i)
    : Rbar = R := by
  sorry

end «CAM-Bench-5»
