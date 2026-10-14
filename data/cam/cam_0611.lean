import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-611»

def posynomial (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ K : ℕ, ∃ c : Fin K → ℝ, ∃ a : Fin n → Fin K → ℝ,
    (∀ k : Fin K, 0 < c k) ∧
    ∀ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) →
      f x = ∑ k : Fin K, c k * ∏ i : Fin n, (x i) ^ (a i k)

theorem max_posynomial_minimization_log_change_of_variables_convex
    (n : ℕ) (p q : (Fin n → ℝ) → ℝ)
    (hp : posynomial n p) (hq : posynomial n q)
    (hp_pos : ∀ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) → 0 < p x)
    (hq_pos : ∀ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) → 0 < q x) :
    ∃ K : ℕ, ∃ L : ℕ, ∃ c : Fin K → ℝ, ∃ a : Fin n → Fin K → ℝ,
      ∃ d : Fin L → ℝ, ∃ b : Fin n → Fin L → ℝ,
        (∀ k : Fin K, 0 < c k) ∧
        (∀ l : Fin L, 0 < d l) ∧
        (∀ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) →
          p x = ∑ k : Fin K, c k * ∏ i : Fin n, (x i) ^ (a i k)) ∧
        (∀ x : Fin n → ℝ, (∀ i : Fin n, 0 < x i) →
          q x = ∑ l : Fin L, d l * ∏ i : Fin n, (x i) ^ (b i l)) ∧
        (let Fp : ((Fin n → ℝ) × ℝ) → ℝ :=
            fun ys => Real.log (∑ k : Fin K, c k * Real.exp (∑ i : Fin n, a i k * ys.1 i))
          let Fq : ((Fin n → ℝ) × ℝ) → ℝ :=
            fun ys => Real.log (∑ l : Fin L, d l * Real.exp (∑ i : Fin n, b i l * ys.1 i))
          ConvexOn ℝ Set.univ Fp ∧
          ConvexOn ℝ Set.univ Fq ∧
          (∀ x : Fin n → ℝ, ∀ t : ℝ, (∀ i : Fin n, 0 < x i) → 0 < t →
            ((∃ y : Fin n → ℝ, ∃ s : ℝ,
                (∀ i : Fin n, x i = Real.exp (y i)) ∧
                t = Real.exp s ∧
                Fp (y, s) ≤ s ∧
                Fq (y, s) ≤ s) ↔
             max (p x) (q x) ≤ t)) ∧
          ((∃ x : Fin n → ℝ, ∃ t : ℝ,
              (∀ i : Fin n, 0 < x i) ∧
              0 < t ∧
              max (p x) (q x) ≤ t ∧
              ∀ z : Fin n → ℝ, ∀ u : ℝ,
                (∀ i : Fin n, 0 < z i) →
                0 < u →
                max (p z) (q z) ≤ u →
                t ≤ u) ↔
           ∃ y : Fin n → ℝ, ∃ s : ℝ,
              Fp (y, s) ≤ s ∧
              Fq (y, s) ≤ s ∧
              ∀ y' : Fin n → ℝ, ∀ s' : ℝ,
                Fp (y', s') ≤ s' →
                Fq (y', s') ≤ s' →
                s ≤ s')) := by
  sorry

end «CAM-Bench-611»
