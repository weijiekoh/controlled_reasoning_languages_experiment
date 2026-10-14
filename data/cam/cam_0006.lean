import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-6»

def differentiableAtOn
    {n m : ℕ}
    (g : (Fin n → ℝ) → (Fin m → ℝ))
    (s : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ s, ∃ A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ),
    Tendsto
      (fun h : Fin n → ℝ =>
        ‖g (x + h) - g x - A h‖ / ‖h‖)
      (𝓝[≠] (0 : Fin n → ℝ))
      (𝓝 (0 : ℝ))

def lipschitzContinuousOn
    {n p : ℕ}
    (g : (Fin n → ℝ) → (Fin p → ℝ))
    (s : Set (Fin n → ℝ))
    (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ L * ‖x - y‖

def lipschitzContinuousGradientOn
    {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (s : Set (EuclideanSpace ℝ (Fin n)))
    (L : ℝ) : Prop :=
  DifferentiableOn ℝ g s ∧
    0 ≤ L ∧ ∀ x ∈ s, ∀ y ∈ s, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖

def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, (x i)^2)

def inducedOperatorNorm
    {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin n → ℝ, euclideanNorm x ≤ 1 ∧ r = euclideanNorm (A x)}

theorem jacobian_and_gradient_lipschitz_bounds
    {m n : ℕ}
    {L M : ℝ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (r : Fin m → (EuclideanSpace ℝ (Fin n) → ℝ))
    (hne : D.Nonempty)
    (hcompact : IsCompact D)
    (hdiff : ∀ j : Fin m, DifferentiableOn ℝ (r j) D)
    (hLip_grad :
      ∀ j : Fin m, ∀ x ∈ D, ∀ y ∈ D,
        ‖gradient (r j) x - gradient (r j) y‖ ≤ L * ‖x - y‖)
    (hLip_r : ∀ j : Fin m, ∀ x ∈ D, ∀ y ∈ D, |r j x - r j y| ≤ L * ‖x - y‖)
    (hbound : ∀ j : Fin m, ∀ x ∈ D, |r j x| ≤ M)
    (hL : 0 < L)
    (hM : 0 < M) :
    (∀ x ∈ D, ∀ y ∈ D,
      inducedOperatorNorm
        (Matrix.toLin'
          ((Matrix.of fun j i => gradient (r j) x i) -
            (Matrix.of fun j i => gradient (r j) y i)))
        ≤ Real.sqrt m * L * ‖x - y‖) ∧
    (∀ x ∈ D, ∀ y ∈ D,
      ‖(∑ j : Fin m, r j x • gradient (r j) x) -
          (∑ j : Fin m, r j y • gradient (r j) y)‖
        ≤ (m : ℝ) * L * (M + L) * ‖x - y‖) := by
  sorry

end «CAM-Bench-6»
