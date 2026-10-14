import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-204»

def optimalValue {α : Type*} (φ : α → ℝ) (C : Set α) (maximize : Bool) : EReal :=
  if maximize then sSup ((fun x => (φ x : EReal)) '' C) else sInf ((fun x => (φ x : EReal)) '' C)

def IsOptimalSolution {α : Type*} (φ : α → ℝ) (C : Set α) (maximize : Bool) (xStar : α) : Prop :=
  xStar ∈ C ∧ (φ xStar : EReal) = optimalValue φ C maximize

def feasibleSet {α : Type*} (constraints : Set (Set α)) : Set α :=
  {x | ∀ S ∈ constraints, x ∈ S}

structure NetworkUtilityMaximizationProblem where
  n : ℕ
  R : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ

def NetworkUtilityMaximizationProblem.feasibleSet
    (P : NetworkUtilityMaximizationProblem) : Set (Fin P.n → ℝ) :=
  {f | (∀ j, 0 < f j) ∧ ∀ i, ∑ j, P.R i j * f j < P.c i}

def NetworkUtilityMaximizationProblem.objective
    (_P : NetworkUtilityMaximizationProblem) (f : Fin _P.n → ℝ) : ℝ :=
  ∑ j, Real.log (f j)

theorem network_utility_feasible_set_convex
    (m n : ℕ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin m → ℝ)
    (hR : ∀ i j, R i j = 1 ∨ R i j = 0)
    (hc : ∀ i, 0 < c i)
    (hne : ({f : Fin n → ℝ | (∀ j, 0 < f j) ∧ ∀ i, ∑ j, R i j * f j < c i}).Nonempty) :
    Convex ℝ {f : Fin n → ℝ | (∀ j, 0 < f j) ∧ ∀ i, ∑ j, R i j * f j < c i} := by
  sorry

end «CAM-Bench-204»
