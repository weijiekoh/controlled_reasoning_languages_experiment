import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-628»

def feasibleSet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b c : Fin n → ℝ) (a : ℝ) :
    Set (Fin n → ℝ) :=
  {x | A.mulVec x ≤ b ∧ dotProduct c x = a}

structure ParametricSupremumProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  Y : (Fin n → ℝ) → ℝ
  c_nonneg : ∀ i : Fin n, 0 ≤ c i
  Y_nonneg : ∀ x : Fin n → ℝ, 0 ≤ Y x
  Y_logConcave :
    ∀ x₁ x₂ : Fin n → ℝ, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      Y (θ • x₁ + (1 - θ) • x₂) ≥
        Real.rpow (Y x₁) θ * Real.rpow (Y x₂) (1 - θ)
  cTx_pos_on_feasible :
    ∀ ⦃x : Fin n → ℝ⦄, A.mulVec x ≤ b → 0 < dotProduct c x
  Y_pos_on_feasible :
    ∀ ⦃x : Fin n → ℝ⦄, A.mulVec x ≤ b → 0 < Y x
  finite_when_nonempty :
    ∀ a : ℝ,
      {x : Fin n → ℝ | A.mulVec x ≤ b ∧ dotProduct c x = a}.Nonempty →
        BddAbove (Y '' {x : Fin n → ℝ | A.mulVec x ≤ b ∧ dotProduct c x = a})

def ParametricSupremumProblem.C (p : ParametricSupremumProblem) : Set (Fin p.n → ℝ) :=
  {x | p.A.mulVec x ≤ p.b}

def ParametricSupremumProblem.isFeasible
    (p : ParametricSupremumProblem) (a : ℝ) (x : Fin p.n → ℝ) : Prop :=
  x ∈ p.C ∧ dotProduct p.c x = a

def ParametricSupremumProblem.feasibleSet
    (p : ParametricSupremumProblem) (a : ℝ) : Set (Fin p.n → ℝ) :=
  {x | p.isFeasible a x}

def ParametricSupremumProblem.valueSet
    (p : ParametricSupremumProblem) (a : ℝ) : Set ℝ :=
  p.Y '' p.feasibleSet a

def ParametricSupremumProblem.f
    (p : ParametricSupremumProblem) (a : ℝ) : ℝ := by
  classical
  exact if h : (p.feasibleSet a).Nonempty then sSup (p.valueSet a) else 0

theorem ParametricSupremumProblem.f_logConcave
    (p : ParametricSupremumProblem) :
    ∀ a₁ a₂ : ℝ, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      p.f (θ * a₁ + (1 - θ) * a₂) ≥
        Real.rpow (p.f a₁) θ * Real.rpow (p.f a₂) (1 - θ) := by
  sorry

end «CAM-Bench-628»
