import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-664»

namespace Exercise_6_7__a_

open scoped BigOperators

theorem tikhonov_svd_has_unique_minimizer
    {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m))
    (δ : ℝ)
    (σ : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℝ (Fin m))
    (v : Fin r → EuclideanSpace ℝ (Fin n))
    (hδ : 0 < δ)
    (hA :
      A = ∑ i : Fin r,
        σ i • Matrix.vecMulVec (u i) (v i))
    (hσ : ∀ i : Fin r, 0 < σ i)
    (hu_orthonormal : Orthonormal ℝ u)
    (hv_orthonormal : Orthonormal ℝ v) :
    ∃! x : EuclideanSpace ℝ (Fin n),
      (∀ y : EuclideanSpace ℝ (Fin n),
        ‖A.mulVec x - b‖ ^ 2 + δ * ‖x‖ ^ 2 ≤ ‖A.mulVec y - b‖ ^ 2 + δ * ‖y‖ ^ 2) ∧
      x =
        ∑ i : Fin r,
          ((σ i) / ((σ i) ^ 2 + δ) * ⟪u i, b⟫) • v i := by
  sorry

end Exercise_6_7__a_

end «CAM-Bench-664»
