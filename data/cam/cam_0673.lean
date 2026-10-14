import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-673»

def logLikelihood {Θ Y : Type} (p : Θ → Y → ℝ) (y : Fin N → Y) : Θ → ℝ :=
  fun θ => ∑ i : Fin N, Real.log (p θ (y i))

def JointlyConcave {X Y : Type*} [AddCommMonoid X] [Module ℝ X] [AddCommMonoid Y] [Module ℝ Y]
    (f : X × Y → ℝ) : Prop :=
  ∀ (x₁ x₂ : X) (y₁ y₂ : Y) (lam : ℝ),
    0 ≤ lam →
    lam ≤ 1 →
    f (lam • x₁ + (1 - lam) • x₂, lam • y₁ + (1 - lam) • y₂) ≥
      lam * f (x₁, y₁) + (1 - lam) * f (x₂, y₂)

theorem gaussian_logLikelihood_jointly_concave_on_covariance_region
    {n N : ℕ}
    (y : Fin N → (Fin n → ℝ)) :
    let p : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → (Fin n → ℝ) → ℝ :=
      fun θ z =>
        (2 * Real.pi) ^ (-(n : ℝ) / 2) *
          Real.sqrt (Matrix.det θ.1)⁻¹ *
          Real.exp
            (-((∑ i : Fin n, ∑ j : Fin n, (z i - θ.2 i) * ((θ.1)⁻¹ i j) * (z j - θ.2 j)) / 2))
    let l : (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) → ℝ :=
      logLikelihood p y
    let Ybar : Fin n → ℝ :=
      fun j => (1 / (N : ℝ)) * ∑ i : Fin N, y i j
    let sampleCov : Matrix (Fin n) (Fin n) ℝ :=
      fun j k =>
        (1 / (N : ℝ)) * ∑ i : Fin N, (y i j - Ybar j) * (y i k - Ybar k)
    ∀ (R₁ R₂ : Matrix (Fin n) (Fin n) ℝ) (a₁ a₂ : Fin n → ℝ) (lam : ℝ),
      R₁.IsSymm →
      R₂.IsSymm →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i : Fin n, ∑ j : Fin n, x i * R₁ i j * x j) →
      (∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i : Fin n, ∑ j : Fin n, x i * R₂ i j * x j) →
      (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * ((2 : ℝ) • sampleCov - R₁) i j * x j) →
      (∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * ((2 : ℝ) • sampleCov - R₂) i j * x j) →
      0 ≤ lam →
      lam ≤ 1 →
      l (lam • R₁ + (1 - lam) • R₂, lam • a₁ + (1 - lam) • a₂) ≥
        lam * l (R₁, a₁) + (1 - lam) * l (R₂, a₂) := by
  sorry

end «CAM-Bench-673»
