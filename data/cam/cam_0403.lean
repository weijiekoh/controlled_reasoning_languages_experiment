import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-403»

theorem kktBlockMatrix_pos_neg_eigenvalue_counts
    {n p : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ)
    (hP_symm : P.IsSymm)
    (hP_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P.mulVec x))
    (hA_rank : Matrix.rank A = p)
    (hpn : p < n)
    (hK_nonsingular :
      IsUnit
        (Matrix.det
          (Matrix.fromBlocks P A.transpose A (0 : Matrix (Fin p) (Fin p) ℝ)))) :
    let K : Matrix (Sum (Fin n) (Fin p)) (Sum (Fin n) (Fin p)) ℝ :=
      Matrix.fromBlocks P A.transpose A (0 : Matrix (Fin p) (Fin p) ℝ)
    Multiset.countP (fun μ : ℝ => 0 < μ) K.charpoly.roots = n ∧
      Multiset.countP (fun μ : ℝ => μ < 0) K.charpoly.roots = p := by
  sorry

end «CAM-Bench-403»
