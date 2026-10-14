import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-348»

def IsMaximumLikelihoodEstimate {Θ Y : Type*} (p : Y → Θ → ℝ) (s : Set Θ) (y : Y) (θhat : Θ) : Prop :=
  θhat ∈ s ∧ ∀ θ ∈ s, p y θ ≤ p y θhat

def IsLogMaximumLikelihoodEstimate {Θ Y : Type*} (p : Y → Θ → ℝ) (s : Set Θ) (y : Y) (θhat : Θ) : Prop :=
  θhat ∈ s ∧ ∀ θ ∈ s, Real.log (p y θ) ≤ Real.log (p y θhat)

structure TeamAbilityMaximumLikelihoodProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  σ : ℝ

def TeamAbilityMaximumLikelihoodProblem.IsFeasible
    (P : TeamAbilityMaximumLikelihoodProblem) (a : Fin P.n → ℝ) : Prop :=
  ∀ j, 0 ≤ a j ∧ a j ≤ 1

def TeamAbilityMaximumLikelihoodProblem.probitArgument
    (P : TeamAbilityMaximumLikelihoodProblem) (a : Fin P.n → ℝ) (i : Fin P.m) : ℝ :=
  (∑ j, P.A i j * a j) / P.σ

def normalCDF (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(t ^ 2) / 2)

def TeamAbilityMaximumLikelihoodProblem.minObjective
    (P : TeamAbilityMaximumLikelihoodProblem) (a : Fin P.n → ℝ) : ℝ :=
  ∑ i, -Real.log (normalCDF (P.probitArgument a i))

def TeamAbilityMaximumLikelihoodProblem.maxObjective
    (P : TeamAbilityMaximumLikelihoodProblem) (a : Fin P.n → ℝ) : ℝ :=
  ∑ i, Real.log (normalCDF (P.probitArgument a i))

theorem teamAbilityMaximumLikelihoodProblem_gives_mle
    (P : TeamAbilityMaximumLikelihoodProblem)
    (ahat : Fin P.n → ℝ)
    (hσ : 0 < P.σ) :
    IsMaximumLikelihoodEstimate
      (fun _ a => Real.exp (-P.minObjective a))
      {a | P.IsFeasible a}
      P
      ahat ↔
      ahat ∈ {a | P.IsFeasible a} ∧
        ∀ a, P.IsFeasible a → P.minObjective ahat ≤ P.minObjective a := by
  sorry

end «CAM-Bench-348»
