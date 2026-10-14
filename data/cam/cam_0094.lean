import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-94»

structure QuasiNewtonMethod where
  dim : ℕ
  fVec : EuclideanSpace ℝ (Fin dim) → ℝ
  xVec : ℕ → EuclideanSpace ℝ (Fin dim)
  BVec : ℕ → EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim)
  pVec : ℕ → EuclideanSpace ℝ (Fin dim)
  gradVec : ℕ → EuclideanSpace ℝ (Fin dim)
  gradVec_eq : ∀ k, HasGradientAt (f := fVec) (gradVec k) (xVec k)
  updateRule :
    ℕ →
      (EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim)) →
      EuclideanSpace ℝ (Fin dim) →
      EuclideanSpace ℝ (Fin dim) →
      EuclideanSpace ℝ (Fin dim) →
      EuclideanSpace ℝ (Fin dim) →
      (EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim))
  search_direction_eq_vec : ∀ k, BVec k (pVec k) = -gradVec k
  B_updated_from_previous :
    ∀ k,
      BVec (k + 1) =
        updateRule k (BVec k) (xVec k) (xVec (k + 1)) (gradVec k) (gradVec (k + 1))

def QuasiNewtonMethod.x (_q : QuasiNewtonMethod) : ℕ → ℝ :=
  fun _ => 0

def QuasiNewtonMethod.grad (_q : QuasiNewtonMethod) : ℕ → ℝ :=
  fun _ => 0

def QuasiNewtonMethod.B (_q : QuasiNewtonMethod) : ℕ → ℝ :=
  fun _ => 0

def quasiNewtonMethod : Set QuasiNewtonMethod :=
  { q | ∀ k, q.BVec k (q.pVec k) = -q.gradVec k }

structure HessianApproximation (n : ℕ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  B : ℕ → Matrix (Fin n) (Fin n) ℝ
  hessian : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  hessian_spec :
    ∀ k : ℕ, HasFDerivAt (gradient f) (hessian k) (x k)
  approximationResidual :
    ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  approximation_decomposition :
    ∀ k : ℕ,
      Matrix.toEuclideanLin (B k) = hessian k + approximationResidual k

def sr1Update (q : QuasiNewtonMethod) (k : ℕ)
    (hdenom :
      let s := q.xVec (k + 1) - q.xVec k
      let y := q.gradVec (k + 1) - q.gradVec k
      let u := y - q.BVec k s
      ⟪u, s⟫ ≠ 0) :
    EuclideanSpace ℝ (Fin q.dim) →L[ℝ] EuclideanSpace ℝ (Fin q.dim) :=
  let s := q.xVec (k + 1) - q.xVec k
  let y := q.gradVec (k + 1) - q.gradVec k
  let u := y - q.BVec k s
  q.BVec k + (1 / ⟪u, s⟫) • (((innerSL ℝ) u).smulRight u)

def bfgsUpdate (q : QuasiNewtonMethod) (k : ℕ)
    (hBs :
      let s := q.xVec (k + 1) - q.xVec k
      ⟪q.BVec k s, s⟫ ≠ 0)
    (hys :
      let s := q.xVec (k + 1) - q.xVec k
      let y := q.gradVec (k + 1) - q.gradVec k
      ⟪y, s⟫ ≠ 0) :
    EuclideanSpace ℝ (Fin q.dim) →L[ℝ] EuclideanSpace ℝ (Fin q.dim) :=
  let s := q.xVec (k + 1) - q.xVec k
  let y := q.gradVec (k + 1) - q.gradVec k
  q.BVec k
    - (1 / ⟪q.BVec k s, s⟫) • (((innerSL ℝ) (q.BVec k s)).smulRight (q.BVec k s))
    + (1 / ⟪y, s⟫) • (((innerSL ℝ) y).smulRight y)

structure SymmetricRankOneUpdate (n : ℕ) where
  B : ℕ → Matrix (Fin n) (Fin n) ℝ
  u : ℕ → Fin n → ℝ
  α : ℕ → ℝ
  alpha_ne_zero : ∀ k, α k ≠ 0
  update_eq : ∀ k, B (k + 1) = B k + (1 / α k) • Matrix.vecMulVec (u k) (u k)

def scaleInvariantUnderAffineChange (x z : ℕ → ℝ) (S s : ℝ) : Prop :=
  ∀ k, x k = S * z k + s

theorem sr1_and_bfgs_scale_invariant
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n))
    (ftilde : EuclideanSpace ℝ (Fin n) → ℝ)
    (x x_tilde : ℕ → EuclideanSpace ℝ (Fin n))
    (p p_tilde : ℕ → EuclideanSpace ℝ (Fin n))
    (grad grad_tilde : ℕ → EuclideanSpace ℝ (Fin n))
    (B B_tilde : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hf_diff : ∀ x, DifferentiableAt ℝ f x)
    (hS_nonsing : Function.Bijective S)
    (hftilde : ∀ z, ftilde z = f (S z + s))
    (hx0 : x 0 = S (x_tilde 0) + s)
    (hB0 :
      B_tilde 0 = (S.adjoint.comp (B 0)).comp S)
    (hunit_x : ∀ k, x (k + 1) = x k + p k)
    (hunit_tilde : ∀ k, x_tilde (k + 1) = x_tilde k + p_tilde k)
    (hsearch_x : ∀ k, B k (p k) = -grad k)
    (hsearch_tilde : ∀ k, B_tilde k (p_tilde k) = -grad_tilde k)
    (hgrad_x : ∀ k, HasGradientAt f (grad k) (x k))
    (hgrad_ftilde : ∀ k, HasGradientAt ftilde (grad_tilde k) (x_tilde k))
    (hsr1_x :
      ∀ k,
        let sk := x (k + 1) - x k
        let yk := grad (k + 1) - grad k
        ⟪yk - B k sk, sk⟫ ≠ 0)
    (hsr1_tilde :
      ∀ k,
        let sk := x_tilde (k + 1) - x_tilde k
        let yk := grad_tilde (k + 1) - grad_tilde k
        ⟪yk - B_tilde k sk, sk⟫ ≠ 0)
    (hbfgs_x1 :
      ∀ k,
        let sk := x (k + 1) - x k
        ⟪B k sk, sk⟫ ≠ 0)
    (hbfgs_x2 :
      ∀ k,
        let sk := x (k + 1) - x k
        let yk := grad (k + 1) - grad k
        ⟪yk, sk⟫ ≠ 0)
    (hbfgs_tilde1 :
      ∀ k,
        let sk := x_tilde (k + 1) - x_tilde k
        ⟪B_tilde k sk, sk⟫ ≠ 0)
    (hbfgs_tilde2 :
      ∀ k,
        let sk := x_tilde (k + 1) - x_tilde k
        let yk := grad_tilde (k + 1) - grad_tilde k
        ⟪yk, sk⟫ ≠ 0)
    (hupdate :
      (((∀ k,
          let sk := x (k + 1) - x k
          let yk := grad (k + 1) - grad k
          let uk := yk - B k sk
          B (k + 1) = B k + (1 / ⟪uk, sk⟫) • (((innerSL ℝ) uk).smulRight uk)) ∧
        (∀ k,
          let sk := x_tilde (k + 1) - x_tilde k
          let yk := grad_tilde (k + 1) - grad_tilde k
          let uk := yk - B_tilde k sk
          B_tilde (k + 1) =
            B_tilde k + (1 / ⟪uk, sk⟫) • (((innerSL ℝ) uk).smulRight uk))) ∨
       ((∀ k,
          let sk := x (k + 1) - x k
          let yk := grad (k + 1) - grad k
          B (k + 1) =
            B k
              - (1 / ⟪B k sk, sk⟫) • (((innerSL ℝ) (B k sk)).smulRight (B k sk))
              + (1 / ⟪yk, sk⟫) • (((innerSL ℝ) yk).smulRight yk)) ∧
        (∀ k,
          let sk := x_tilde (k + 1) - x_tilde k
          let yk := grad_tilde (k + 1) - grad_tilde k
          B_tilde (k + 1) =
            B_tilde k
              - (1 / ⟪B_tilde k sk, sk⟫) • (((innerSL ℝ) (B_tilde k sk)).smulRight (B_tilde k sk))
              + (1 / ⟪yk, sk⟫) • (((innerSL ℝ) yk).smulRight yk))))
    )
    :
    ∀ k, x k = S (x_tilde k) + s := by
  sorry

end «CAM-Bench-94»
