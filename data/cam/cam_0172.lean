import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-172»

def Quasilinear {E : Type*} [AddCommMonoid E] [SMul ℝ E] (C : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ C ∧
    ∀ ⦃x y : E⦄, x ∈ C → y ∈ C →
      ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
        min (f x) (f y) ≤ f (θ • x + (1 - θ) • y) ∧
          f (θ • x + (1 - θ) • y) ≤ max (f x) (f y)

def Quasiconvex {E : Type*} [AddCommMonoid E] [SMul ℝ E] (C : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ C → y ∈ C →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      f (θ • x + (1 - θ) • y) ≤ max (f x) (f y)

def Quasiconcave {E : Type*} [AddCommMonoid E] [SMul ℝ E] (C : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ C → y ∈ C →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      min (f x) (f y) ≤ f (θ • x + (1 - θ) • y)

theorem irr_quasilinear
    (n : ℕ) (hn : 1 ≤ n)
    (F : Set (Fin (n + 1) → ℝ))
    (IRR : (Fin (n + 1) → ℝ) → ℝ)
    (hF :
      ∀ x : Fin (n + 1) → ℝ,
        x ∈ F ↔
          x 0 < 0 ∧
            (∀ j : Fin (n + 1), j ≠ 0 → 0 ≤ x j) ∧
            0 < ∑ j : Fin (n + 1), x j)
    (hIRR :
      ∀ x : Fin (n + 1) → ℝ, x ∈ F →
        ∃! r : ℝ, -1 < r ∧
          ∑ j : Fin (n + 1), x j / (1 + r) ^ (j : ℕ) = 0)
    (hIRR_def :
      ∀ x : Fin (n + 1) → ℝ, x ∈ F →
        -1 < IRR x ∧
          ∑ j : Fin (n + 1), x j / (1 + IRR x) ^ (j : ℕ) = 0)
    (hIRR_unique :
      ∀ x : Fin (n + 1) → ℝ, x ∈ F →
        ∀ r : ℝ, -1 < r →
          (∑ j : Fin (n + 1), x j / (1 + r) ^ (j : ℕ) = 0) → r = IRR x) :
    ∀ ⦃x y : Fin (n + 1) → ℝ⦄, x ∈ F → y ∈ F →
      ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
        θ • x + (1 - θ) • y ∈ F →
          min (IRR x) (IRR y) ≤ IRR (θ • x + (1 - θ) • y) ∧
            IRR (θ • x + (1 - θ) • y) ≤ max (IRR x) (IRR y) := by
  sorry

end «CAM-Bench-172»
