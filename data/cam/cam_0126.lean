import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-126»

open BigOperators

theorem polynomial_preconditioned_quadratic_form_has_eigenpairs
    {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin (k + 1) → ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin n))
    (lam : Fin n → ℝ)
    (hA_symm : A.IsSymm)
    (hv_orthonormal : Orthonormal ℝ v)
    (hv_basis : Submodule.span ℝ (Set.range v) = ⊤)
    (hAv : ∀ i : Fin n, Matrix.toEuclideanLin A (v i) = lam i • v i) :
    ∀ i : Fin n,
      Matrix.toEuclideanLin
        (((1 + ((∑ j : Fin (k + 1), (a j) • (A ^ (j : ℕ))) * A)).transpose) *
          (A * (1 + ((∑ j : Fin (k + 1), (a j) • (A ^ (j : ℕ))) * A))))
        (v i) =
        (lam i * (1 + lam i * ∑ j : Fin (k + 1), a j * (lam i ^ (j : ℕ))) ^ 2) • v i := by
  sorry

end «CAM-Bench-126»
