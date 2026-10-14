import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-251»

def IsLogConcaveDensity {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : (Fin n → ℝ) → NNReal,
    (f = fun x => (g x : ℝ)) ∧
      ∀ x y : Fin n → ℝ, ∀ θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            (g (θ • x + (1 - θ) • y) : ℝ) ≥
              (g x : ℝ) ^ θ * (g y : ℝ) ^ (1 - θ)

def IsLogConcaveOn {n : ℕ} (D : Set (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) : Prop :=
  Convex ℝ D ∧
    (∀ a ∈ D, ∀ b ∈ D, ∀ θ : ℝ,
      0 ≤ θ →
        θ ≤ 1 →
          φ (θ • a + (1 - θ) • b) ≥ (φ a) ^ θ * (φ b) ^ (1 - θ)) ∧
    (∀ a ∈ D, 0 ≤ φ a)

theorem positivePartExpectation_convex_and_logConcave
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → ℝ)
    (φ : ℝ → ℝ)
    (hf : IsLogConcaveDensity f)
    (hf_density : ∫ x, f x = 1)
    (hg : ConcaveOn ℝ Set.univ g)
    (hφ : ∀ a : ℝ, φ a = ∫ x, max (g x - a) 0 * f x) :
    (∀ a : ℝ, 0 ≤ φ a) ∧
      (∀ a b θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            φ (θ * a + (1 - θ) * b) ≤ θ * φ a + (1 - θ) * φ b) ∧
      (∀ a b θ : ℝ,
        0 ≤ θ →
          θ ≤ 1 →
            φ (θ * a + (1 - θ) * b) ≥
              Real.rpow (φ a) θ * Real.rpow (φ b) (1 - θ)) := by
  sorry

end «CAM-Bench-251»
