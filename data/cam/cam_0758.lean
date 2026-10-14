import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-758»

open scoped RealInnerProductSpace

def IsDescentDirection {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) : Prop :=
  ⟪gradient f x, p⟫ < 0

def SatisfiesWolfeConditions {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ c₂ α : ℝ) : Prop :=
  0 < α ∧
    0 < c₁ ∧
    c₁ < c₂ ∧
    c₂ < 1 ∧
    f (x + α • p) ≤ f x + c₁ * α * ⟪gradient f x, p⟫ ∧
    c₂ * ⟪gradient f x, p⟫ ≤ ⟪gradient f (x + α • p), p⟫

def SatisfiesArmijoCondition {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ α : ℝ) : Prop :=
  0 < α ∧
    0 < c₁ ∧
    c₁ < 1 ∧
    f (x + α • p) ≤ f x + c₁ * α * ⟪gradient f x, p⟫

def SatisfiesCurvatureCondition {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₂ α : ℝ) : Prop :=
  0 < α ∧
    0 < c₂ ∧
    c₂ < 1 ∧
    c₂ * ⟪gradient f x, p⟫ ≤ ⟪gradient f (x + α • p), p⟫

theorem exists_stepSize_satisfying_wolfe_conditions
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ c₂ : ℝ)
    (hf : Differentiable ℝ f)
    (hdesc : IsDescentDirection f x p)
    (hbounded : BddBelow (Set.range fun α : Set.Ici (0 : ℝ) => f (x + (α : ℝ) • p)))
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ α : ℝ, SatisfiesWolfeConditions f x p c₁ c₂ α := by
  sorry

end «CAM-Bench-758»
