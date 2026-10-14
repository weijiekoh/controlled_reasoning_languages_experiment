import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-203»

theorem eigenvalue_minimization_sdp_reformulation {n : ℕ} (hn : 1 ≤ n)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hW_symm : Wᵀ = W)
    (hW_nonneg : ∀ i j, 0 ≤ W i j)
    (hW_diag : ∀ i : Fin n, W i i = 0) :
    let one : Fin n → ℝ := fun _ => 1
    let L : Matrix (Fin n) (Fin n) ℝ :=
      -W + Matrix.diagonal (fun i => ∑ j : Fin n, W i j * one j)
    sInf {r : ℝ | ∃ x : Fin n → ℝ,
      (∑ i : Fin n, x i) = 0 ∧
      (∑ i : Fin n, x i ^ 2) = 1 ∧
      r = ∑ i : Fin n, ∑ j : Fin n, x i * L i j * x j} =
    sInf {t : ℝ | ∃ v : Fin n → ℝ,
      (∑ i : Fin n, v i) = 0 ∧
      Matrix.PosSemidef
        (t • (1 : Matrix (Fin n) (Fin n) ℝ) - (L + Matrix.diagonal v))} := by
  sorry

end «CAM-Bench-203»
