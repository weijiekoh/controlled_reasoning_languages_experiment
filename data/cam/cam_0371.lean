import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-371»

def StronglyConvexOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ m : ℝ,
    0 < m ∧
      ∀ x y : EuclideanSpace ℝ (Fin n), ∀ lam : ℝ,
        0 ≤ lam → lam ≤ 1 →
          f (lam • x + (1 - lam) • y) ≤
            lam * f x + (1 - lam) * f y -
              (m / 2) * lam * (1 - lam) * ‖x - y‖ ^ 2

def SmoothOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧
    ∃ L : ℝ,
      0 ≤ L ∧
        ∀ x y : EuclideanSpace ℝ (Fin n),
          ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖

def NewtonStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hess : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hess_inv :
      ∀ _ : EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (h_inv :
      ∀ x : EuclideanSpace ℝ (Fin n),
        Function.LeftInverse (hess_inv x) (hess x) ∧
          Function.RightInverse (hess_inv x) (hess x))
    (x0 : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x0
  | k + 1 =>
      let xk := NewtonStep f grad hess hess_inv h_inv x0 k
      xk - hess_inv xk (grad xk)

def NewtonMethod {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hess : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hess_inv :
      EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x0 : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x0
  | k + 1 =>
      let xk := NewtonMethod f hess hess_inv x0 k
      xk - hess_inv xk (gradient f xk)

def DampedNewtonDirection {n : ℕ} (_f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (grad : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hess_inv :
      EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  -(hess_inv x (grad x))

def DampedNewtonStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (gradx : EuclideanSpace ℝ (Fin n))
    (hess_inv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  x + t • DampedNewtonDirection f x (fun _ => gradx) (fun _ => hess_inv)

def DampedNewtonMethod {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hess_inv :
      EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (stepSize : ℕ → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x0
  | k + 1 =>
      let xk := DampedNewtonMethod f hess_inv stepSize x0 k
      DampedNewtonStep f xk (gradient f xk) (hess_inv xk) (stepSize k)

def BacktrackingLineSearch {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (direction : EuclideanSpace ℝ (Fin n))
    (grad : EuclideanSpace ℝ (Fin n))
    (α β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧
    0 < α ∧ α < (1 / 2 : ℝ) ∧
      ∃ k : ℕ,
        f (x + (β ^ k : ℝ) • direction) ≤
          f x + α * (β ^ k : ℝ) * ⟪grad, direction⟫ ∧
        ∀ j : ℕ, j < k →
          ¬ (f (x + (β ^ j : ℝ) • direction) ≤
            f x + α * (β ^ j : ℝ) * ⟪grad, direction⟫)

open scoped RealInnerProductSpace

def ArmijoCondition {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p grad : EuclideanSpace ℝ (Fin n)) (α t : ℝ) : Prop :=
  0 < t ∧
    0 < α ∧ α < 1 ∧
      f (x + t • p) ≤ f x + α * t * ⟪grad, p⟫

def ScalarNewtonMethod
    (f : ℝ → ℝ) (deriv : ℝ → ℝ) (secondDeriv : ℝ → ℝ)
    (xStar x0 : ℝ) (hx0_lt_xStar : x0 < xStar) : ℕ → ℝ
  | 0 => x0
  | k + 1 => ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k
      - deriv (ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k) /
          secondDeriv (ScalarNewtonMethod f deriv secondDeriv xStar x0 hx0_lt_xStar k)

structure ScalarDampedNewtonBacktracking where
  f : ℝ → ℝ
  deriv : ℝ → ℝ
  secondDeriv : ℝ → ℝ
  α : ℝ
  β : ℝ
  x0 : ℝ
  hα : 0 < α ∧ α < (1 / 2 : ℝ)
  hβ : 0 < β ∧ β < 1
  x : ℕ → ℝ
  t : ℕ → ℝ
  hx0 : x 0 = x0
  ht_bounds : ∀ k : ℕ, 0 < t k ∧ t k ≤ 1
  hstep : ∀ k : ℕ,
    x (k + 1) = x k + t k * (-deriv (x k) / secondDeriv (x k))
  ht_first : ∀ k : ℕ,
    ∃ m : ℕ,
      t k = β ^ m ∧
      f (x k + t k * (-deriv (x k) / secondDeriv (x k))) ≤
        f (x k) + α * t k * deriv (x k) * (-deriv (x k) / secondDeriv (x k)) ∧
      ∀ j : ℕ, j < m →
        ¬ (f (x k + (β ^ j) * (-deriv (x k) / secondDeriv (x k))) ≤
            f (x k) + α * (β ^ j) * deriv (x k) * (-deriv (x k) / secondDeriv (x k)))

def ScalarDampedNewtonBacktracking.direction (N : ScalarDampedNewtonBacktracking) (x : ℝ) : ℝ :=
  -N.deriv x / N.secondDeriv x

def ScalarDampedNewtonBacktracking.armijoAt (N : ScalarDampedNewtonBacktracking) (x : ℝ)
    (t : ℝ) : Prop :=
  N.f (x + t * N.direction x) ≤ N.f x + N.α * t * N.deriv x * N.direction x

def ScalarDampedNewtonBacktracking.stepSize (N : ScalarDampedNewtonBacktracking) (x : ℝ) : Prop :=
  ∃ k : ℕ,
    let t : ℝ := N.β ^ k
    N.armijoAt x t ∧
      ∀ j : ℕ, j < k → ¬N.armijoAt x (N.β ^ j)

def ScalarDampedNewtonBacktracking.step (N : ScalarDampedNewtonBacktracking) (x : ℝ)
    (t : ℝ) : ℝ :=
  x + t * N.direction x

def ScalarDampedNewtonBacktracking.iterate (N : ScalarDampedNewtonBacktracking)
    (stepSize : ℕ → ℝ) : ℕ → ℝ
  | 0 => N.x0
  | k + 1 => N.step (N.iterate stepSize k) (stepSize k)

theorem scalar_newton_monotone_converges_and_backtracking_unit_steps
    (f : ℝ → ℝ)
    (xStar x0 α β : ℝ)
    (hx0_lt_xStar : x0 < xStar)
    (hC3 : ContDiff ℝ 3 f)
    (hstrong_convex : ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, m ≤ deriv^[2] f x)
    (hsmooth : ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ, deriv^[2] f x ≤ L)
    (hthird_nonpos : ∀ x : ℝ, deriv^[3] f x ≤ 0)
    (hminimizer : ∀ x : ℝ, f xStar ≤ f x)
    (hderiv_xStar : deriv f xStar = 0)
    (hsecond_pos : ∀ x : ℝ, 0 < deriv^[2] f x)
    (hα : 0 < α ∧ α < (1 / 2 : ℝ))
    (hβ : 0 < β ∧ β < 1) :
    (∀ k : ℕ,
      ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar k ≤
        ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar (k + 1) ∧
      ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar (k + 1) ≤ xStar) ∧
    Tendsto (ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar) atTop (𝓝 xStar) ∧

    (∀ N : ScalarDampedNewtonBacktracking,
      N.f = f →
      N.deriv = deriv f →
      N.secondDeriv = deriv^[2] f →
      N.α = α →
      N.β = β →
      N.x0 = x0 →
      N.x = ScalarNewtonMethod f (deriv f) (deriv^[2] f) xStar x0 hx0_lt_xStar →
      ∀ k : ℕ, N.t k = 1) := by
  sorry

end «CAM-Bench-371»
