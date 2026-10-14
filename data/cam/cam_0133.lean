import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-133»

open scoped RealInnerProductSpace

theorem mu_k_ge_one_of_cauchy_schwarz
    {n : Type*} [Fintype n] [DecidableEq n]
    (s_k y_k : EuclideanSpace ℝ n) (B_k : Matrix n n ℝ)
    (hB_symm : B_k.IsSymm)
    (hB_pos : Matrix.PosDef B_k)
    (hB_inv : IsUnit B_k.det)
    (hys : ⟪y_k, s_k⟫ ≠ 0) :
    1 ≤
      ((⟪y_k, Matrix.toEuclideanLin (B_k⁻¹) y_k⟫) *
        (⟪s_k, Matrix.toEuclideanLin B_k s_k⟫)) /
        (⟪y_k, s_k⟫ ^ 2) := by
  sorry

end «CAM-Bench-133»
