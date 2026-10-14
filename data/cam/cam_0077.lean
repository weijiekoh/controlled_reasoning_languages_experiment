import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-77»

structure NonlinearProgram (α : Type*) [AddCommMonoid α] [Module ℝ α] where
  f : α → ℝ
  equalityIndex : Type*
  equalityConstraint : equalityIndex → α → ℝ
  inequalityIndex : Type*
  inequalityConstraint : inequalityIndex → α → ℝ
  nonlinear : ¬ ((∃ a : α →ₗ[ℝ] ℝ, f = a) ∧
    (∀ i : equalityIndex, ∃ a : α →ₗ[ℝ] ℝ, equalityConstraint i = a) ∧
    (∀ i : inequalityIndex, ∃ a : α →ₗ[ℝ] ℝ, inequalityConstraint i = a))

def NonlinearProgram.IsFeasible {α : Type*} [AddCommMonoid α] [Module ℝ α]
    (P : NonlinearProgram α) (x : α) : Prop :=
  (∀ i : P.equalityIndex, P.equalityConstraint i x = 0) ∧
  ∀ i : P.inequalityIndex, 0 ≤ P.inequalityConstraint i x

def IsStationaryPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℝ) (x : E) : Prop :=
  ∀ p : E, ∀ d : ℝ,
    Tendsto
      (fun α : ℝ => (g (x + α • p) - g x) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 d) →
      0 ≤ d

def NonlinearProgram.IsInfeasibleStationaryPoint
    (P : NonlinearProgram ℝ) (h : ℝ → ℝ) (x : ℝ) : Prop :=
  ¬ P.IsFeasible x ∧ IsStationaryPoint h x

def NonlinearProgram.IsInfeasible {α : Type*} [AddCommMonoid α] [Module ℝ α]
    (P : NonlinearProgram α) (x : α) : Prop :=
  (∃ i : P.equalityIndex, P.equalityConstraint i x ≠ 0) ∨
    ∃ i : P.inequalityIndex, P.inequalityConstraint i x < 0

def IsExactPenaltyFunction
    {α : Type*} [AddCommMonoid α] [Module ℝ α]
    (P : NonlinearProgram α) (h : α → ℝ) : Prop :=
  ∃ μbar : ℝ, 0 < μbar ∧
    ∀ μ : ℝ, μbar ≤ μ →
      ∀ x : α,
        (P.IsFeasible x ∧ ∀ y : α, P.IsFeasible y → P.f x ≤ P.f y) →
          ∀ y : α, P.f x + μ * h x ≤ P.f y + μ * h y

structure DifferentiableNonlinearProgram (n : ℕ) where
  equalityIndex : Type*
  inequalityIndex : Type*
  f : (Fin n → ℝ) → ℝ
  equalityConstraint : equalityIndex → (Fin n → ℝ) → ℝ
  inequalityConstraint : inequalityIndex → (Fin n → ℝ) → ℝ
  f_differentiable : Differentiable ℝ f
  equalityConstraint_differentiable :
    ∀ i : equalityIndex, Differentiable ℝ (equalityConstraint i)
  inequalityConstraint_differentiable :
    ∀ i : inequalityIndex, Differentiable ℝ (inequalityConstraint i)
  nonlinear : ¬ ((∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, f = a) ∧
    (∀ i : equalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, equalityConstraint i = a) ∧
    (∀ i : inequalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, inequalityConstraint i = a))

private lemma DifferentiableNonlinearProgram.nonlinear_for_toNonlinearProgram
    {n : ℕ} (P : DifferentiableNonlinearProgram n) :
    ¬ ((∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, P.f = a) ∧
      (∀ i : P.equalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, P.equalityConstraint i = a) ∧
      (∀ i : P.inequalityIndex, ∃ a : (Fin n → ℝ) →ₗ[ℝ] ℝ, P.inequalityConstraint i = a)) :=
  P.nonlinear

def DifferentiableNonlinearProgram.toNonlinearProgram
    {n : ℕ} (P : DifferentiableNonlinearProgram n) :
    NonlinearProgram (Fin n → ℝ) where
  f := P.f
  equalityIndex := P.equalityIndex
  equalityConstraint := P.equalityConstraint
  inequalityIndex := P.inequalityIndex
  inequalityConstraint := P.inequalityConstraint
  nonlinear := by
    exact DifferentiableNonlinearProgram.nonlinear_for_toNonlinearProgram P

def DifferentiableNonlinearProgram.IsFeasible
    {n : ℕ} (P : DifferentiableNonlinearProgram n) (x : Fin n → ℝ) : Prop :=
  P.toNonlinearProgram.IsFeasible x

theorem infeasible_of_eventually_stationary_penalty
    {n : ℕ}
    (P : DifferentiableNonlinearProgram n)
    [Fintype P.equalityIndex] [Fintype P.inequalityIndex]
    (h : (Fin n → ℝ) → ℝ)
    (h_def : h =
      fun x : Fin n → ℝ =>
        (∑ i : P.equalityIndex, |P.equalityConstraint i x|) +
        ∑ i : P.inequalityIndex, max 0 (-P.inequalityConstraint i x))
    (xhat : Fin n → ℝ) (muhat : ℝ)
    (h_muhat_pos : 0 < muhat)
    (h_infeasible : P.toNonlinearProgram.IsInfeasible xhat)
    (h_stationary :
      ∀ μ : ℝ, muhat < μ →
        IsStationaryPoint (fun x : Fin n → ℝ => P.f x + μ * h x) xhat) :
    IsStationaryPoint h xhat := by
  sorry

end «CAM-Bench-77»
