import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-612»

structure ExponentialPosynomialMinimization (n : ℕ) where
  p : (Fin n → ℝ) → ℝ
  q : (Fin n → ℝ) → ℝ

def ExponentialPosynomialMinimization.feasibleSet {n : ℕ}
    (_P : ExponentialPosynomialMinimization n) : Set (Fin n → ℝ) :=
  {x | ∀ i : Fin n, 0 < x i}

def ExponentialPosynomialMinimization.isFeasible {n : ℕ}
    (P : ExponentialPosynomialMinimization n) (x : Fin n → ℝ) : Prop :=
  x ∈ P.feasibleSet

def ExponentialPosynomialMinimization.objective {n : ℕ}
    (P : ExponentialPosynomialMinimization n) (x : Fin n → ℝ) : ℝ :=
  Real.exp (P.p x) + Real.exp (P.q x)

structure ExponentialPosynomialConvexReformulation (n K L : ℕ) where
  c : Fin K → ℝ
  d : Fin L → ℝ
  a : Fin K → Fin n → ℝ
  b : Fin L → Fin n → ℝ

def ExponentialPosynomialConvexReformulation.feasibleSet {n K L : ℕ}
    (P : ExponentialPosynomialConvexReformulation n K L) :
    Set ((Fin n → ℝ) × ℝ × ℝ) :=
  {x |
    (Finset.sum Finset.univ fun k =>
      P.c k * Real.exp (Finset.sum Finset.univ fun i => P.a k i * x.1 i)) ≤ x.2.1 ∧
    (Finset.sum Finset.univ fun l =>
      P.d l * Real.exp (Finset.sum Finset.univ fun i => P.b l i * x.1 i)) ≤ x.2.2}

def ExponentialPosynomialConvexReformulation.firstSum {n K L : ℕ}
    (P : ExponentialPosynomialConvexReformulation n K L) (y : Fin n → ℝ) : ℝ :=
  Finset.sum Finset.univ fun k =>
    P.c k * Real.exp (Finset.sum Finset.univ fun i => P.a k i * y i)

def ExponentialPosynomialConvexReformulation.secondSum {n K L : ℕ}
    (P : ExponentialPosynomialConvexReformulation n K L) (y : Fin n → ℝ) : ℝ :=
  Finset.sum Finset.univ fun l =>
    P.d l * Real.exp (Finset.sum Finset.univ fun i => P.b l i * y i)

def ExponentialPosynomialConvexReformulation.isFeasible {n K L : ℕ}
    (P : ExponentialPosynomialConvexReformulation n K L) (y : Fin n → ℝ) (t₁ t₂ : ℝ) : Prop :=
  P.firstSum y ≤ t₁ ∧ P.secondSum y ≤ t₂

def ExponentialPosynomialConvexReformulation.objective {n K L : ℕ}
    (P : ExponentialPosynomialConvexReformulation n K L) (t₁ t₂ : ℝ) : ℝ :=
  Real.exp t₁ + Real.exp t₂

def ExponentialPosynomialConvexReformulation.toExponentialPosynomialMinimization {n K L : ℕ}
    (P : ExponentialPosynomialConvexReformulation n K L) :
    ExponentialPosynomialMinimization n where
  p := fun y => Real.log (P.firstSum y)
  q := fun y => Real.log (P.secondSum y)

theorem exponential_posynomial_convex_reformulation_equivalent
    {n K L : ℕ} (P : ExponentialPosynomialConvexReformulation n K L)
    (hc : ∀ k : Fin K, 0 < P.c k)
    (hd : ∀ l : Fin L, 0 < P.d l) :
    (∀ x : Fin n → ℝ, (P.toExponentialPosynomialMinimization).isFeasible x ↔ ∀ i : Fin n, 0 < x i) ∧
    (∀ x : Fin n → ℝ, (P.toExponentialPosynomialMinimization).isFeasible x →
      let y : Fin n → ℝ := fun i => Real.log (x i)
      P.isFeasible y
        ((P.toExponentialPosynomialMinimization).p x)
        ((P.toExponentialPosynomialMinimization).q x) ∧
      (P.toExponentialPosynomialMinimization).objective x =
        P.objective
          ((P.toExponentialPosynomialMinimization).p x)
          ((P.toExponentialPosynomialMinimization).q x)) ∧
    (∀ y : Fin n → ℝ, ∀ t₁ t₂ : ℝ, P.isFeasible y t₁ t₂ →
      let x : Fin n → ℝ := fun i => Real.exp (y i)
      (P.toExponentialPosynomialMinimization).isFeasible x ∧
      (P.toExponentialPosynomialMinimization).objective x ≤ P.objective t₁ t₂) ∧
    (∀ y : Fin n → ℝ,
      let x : Fin n → ℝ := fun i => Real.exp (y i)
      (P.toExponentialPosynomialMinimization).objective x =
        P.firstSum y + P.secondSum y) ∧
    (∀ γ : ℝ,
      (∃ x : Fin n → ℝ,
        (P.toExponentialPosynomialMinimization).isFeasible x ∧
        (P.toExponentialPosynomialMinimization).objective x ≤ γ) ↔
      ∃ y : Fin n → ℝ, ∃ t₁ t₂ : ℝ,
        P.isFeasible y t₁ t₂ ∧ P.objective t₁ t₂ ≤ γ) := by
  sorry

end «CAM-Bench-612»
