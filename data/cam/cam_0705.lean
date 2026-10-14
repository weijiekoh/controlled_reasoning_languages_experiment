import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-705»

structure VectorNorm (n : ℕ) where
  norm : (Fin n → ℝ) → ℝ
  nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x
  eq_zero_iff : ∀ x : Fin n → ℝ, norm x = 0 ↔ x = 0
  smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x
  add_le : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y

def IsDualNormValue {n : ℕ} (N : VectorNorm n) (g : Fin n → ℝ) (value : ℝ) : Prop :=
  (∀ d : Fin n → ℝ, N.norm d ≤ 1 → (∑ i, g i * d i) ≤ value) ∧
    ∀ ε : ℝ, 0 < ε → ∃ d : Fin n → ℝ, N.norm d ≤ 1 ∧ value < (∑ i, g i * d i) + ε

structure NormalizedSteepestDescentSubproblem (n : ℕ) where
  norm : VectorNorm n
  gradient : Fin n → ℝ
  step : Fin n → ℝ

def NormalizedSteepestDescentSubproblem.isFeasible
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) (d : Fin n → ℝ) : Prop :=
  P.norm.norm d ≤ 1

def NormalizedSteepestDescentSubproblem.objective
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) (d : Fin n → ℝ) : ℝ :=
  ∑ i, P.gradient i * d i

def NormalizedSteepestDescentSubproblem.optimalValue
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) : ℝ :=
  P.objective P.step

def NormalizedSteepestDescentSubproblem.step_solves_problem
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n) :
    Prop :=
  P.isFeasible P.step ∧
    ∀ d : Fin n → ℝ, P.isFeasible d → P.objective P.step ≤ P.objective d

theorem gradient_dot_scaled_normalized_steepest_descent_eq_neg_dualNorm_sq
    {n : ℕ} (P : NormalizedSteepestDescentSubproblem n)
    (dual : ℝ)
    (hdual : IsDualNormValue P.norm P.gradient dual)
    (hstep_solves : P.step_solves_problem)
    (Δx_sd : Fin n → ℝ)
    (hΔx_sd : Δx_sd = fun i => dual * P.step i) :
    ∑ i, P.gradient i * Δx_sd i = -dual ^ 2 := by
  sorry

end «CAM-Bench-705»
