import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-116»

def steepestDescentIter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (gradf : E → E) (α : ℕ → ℝ) (x : ℕ → E) : Prop :=
  (∀ y : E, gradf y = gradient f y) ∧
  ∀ k : ℕ, x (k + 1) = x k - α k • gradf (x k) ∧ 0 < α k

structure SteepestDescentExactLineSearch (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  f : E → ℝ
  gradf : E → E
  Q : E →ₗ[ℝ] E
  x : ℕ → E
  xStar : E

def SteepestDescentExactLineSearch.alpha {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A : SteepestDescentExactLineSearch E) (k : ℕ) : ℝ :=
  ⟪A.gradf (A.x k), A.gradf (A.x k)⟫ / ⟪A.gradf (A.x k), A.Q (A.gradf (A.x k))⟫

def SteepestDescentExactLineSearch.gradAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A : SteepestDescentExactLineSearch E) (k : ℕ) : E :=
  A.gradf (A.x k)

open scoped BigOperators

theorem steepestDescent_qnorm_update_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : SteepestDescentExactLineSearch E)
    (hiter : steepestDescentIter A.f A.gradf A.alpha A.x)
    (h_ne_star : ∀ k : ℕ, A.x k ≠ A.xStar)
    (Qinv : E →ₗ[ℝ] E)
    (hQ_selfAdjoint : LinearMap.IsSymmetric A.Q)
    (hQ_pos : ∀ v : E, v ≠ 0 → 0 < ⟪v, A.Q v⟫)
    (hQ_left_inv : ∀ v : E, Qinv (A.Q v) = v)
    (hQ_right_inv : ∀ v : E, A.Q (Qinv v) = v)
    (hf_quad :
      ∀ x : E, A.f x - A.f A.xStar = (1 / 2 : ℝ) * ⟪x - A.xStar, A.Q (x - A.xStar)⟫)
    (h_grad_model : ∀ k : ℕ, A.gradAt k = A.Q (A.x k - A.xStar)) :
    ∀ k : ℕ,
      (⟪A.x k - A.xStar, A.Q (A.x k - A.xStar)⟫ -
          ⟪A.x (k + 1) - A.xStar, A.Q (A.x (k + 1) - A.xStar)⟫ =
        2 * A.alpha k * ⟪A.gradAt k, A.Q (A.x k - A.xStar)⟫ -
          (A.alpha k)^2 * ⟪A.gradAt k, A.Q (A.gradAt k)⟫) ∧
      (⟪A.x k - A.xStar, A.Q (A.x k - A.xStar)⟫ -
          ⟪A.x (k + 1) - A.xStar, A.Q (A.x (k + 1) - A.xStar)⟫ =
        (2 * (⟪A.gradAt k, A.gradAt k⟫ ^ 2)) / ⟪A.gradAt k, A.Q (A.gradAt k)⟫ -
          (⟪A.gradAt k, A.gradAt k⟫ ^ 2) / ⟪A.gradAt k, A.Q (A.gradAt k)⟫) ∧
      (⟪A.x k - A.xStar, A.Q (A.x k - A.xStar)⟫ =
        ⟪A.gradAt k, Qinv (A.gradAt k)⟫) ∧
      (⟪A.x (k + 1) - A.xStar, A.Q (A.x (k + 1) - A.xStar)⟫ ≤
        (1 -
            (⟪A.gradAt k, A.gradAt k⟫ ^ 2) /
              (⟪A.gradAt k, A.Q (A.gradAt k)⟫ * ⟪A.gradAt k, Qinv (A.gradAt k)⟫)) *
          ⟪A.x k - A.xStar, A.Q (A.x k - A.xStar)⟫) := by
  sorry

end «CAM-Bench-116»
