import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-184»

def OptimalityConditions {α : Type _} (isOptimal : α → Prop) (conds : α → Prop) : Prop :=
  ∀ ⦃x : α⦄, isOptimal x → conds x

structure LogUtilitySimplexMaximization where
  n : ℕ
  m : ℕ
  p : Fin m → Fin n → ℝ
  π : Fin m → ℝ
  pi_pos : ∀ j : Fin m, 0 < π j
  pi_sum_one : (∑ j : Fin m, π j) = 1
  payoff_pos_on_simplex :
    ∀ x : Fin n → ℝ,
      ((∑ i : Fin n, x i) = 1 ∧ ∀ i : Fin n, 0 ≤ x i) →
      ∀ j : Fin m, 0 < ∑ i : Fin n, p j i * x i

def LogUtilitySimplexMaximization.Feasible (P : LogUtilitySimplexMaximization) (x : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, x i) = 1 ∧ ∀ i : Fin P.n, 0 ≤ x i

def LogUtilitySimplexMaximization.payoff (P : LogUtilitySimplexMaximization) (j : Fin P.m)
    (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, P.p j i * x i

def LogUtilitySimplexMaximization.objective (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.m, P.π j * Real.log (P.payoff j x)

def LogUtilitySimplexMaximization.objectiveDefined (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : Prop :=
  ∀ j : Fin P.m, 0 < P.payoff j x

def LogUtilitySimplexMaximization.isOptimal (P : LogUtilitySimplexMaximization)
    (x : Fin P.n → ℝ) : Prop :=
  P.Feasible x ∧ P.objectiveDefined x ∧
    ∀ y : Fin P.n → ℝ, P.Feasible y → P.objectiveDefined y → P.objective y ≤ P.objective x

theorem logUtilitySimplexMaximization_optimality_conditions
    (P : LogUtilitySimplexMaximization) :
    OptimalityConditions P.isOptimal
      (fun x =>
        ∀ i : Fin P.n,
          (0 < x i →
            (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) = 1) ∧
          (x i = 0 →
            (∑ j : Fin P.m, P.π j * (P.p j i / P.payoff j x)) ≤ 1)) := by
  sorry

end «CAM-Bench-184»
