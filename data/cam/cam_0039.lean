import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-39»

structure SlackVariableForm where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

def SlackVariableForm.feasibleSet (P : SlackVariableForm) : Set (Fin P.n → ℝ) :=
  {x | (∀ i : Fin P.m, ∑ j : Fin P.n, P.A i j * x j = P.b i) ∧
    ∀ j : Fin P.n, 0 ≤ x j}

def SlackVariableForm.objective (P : SlackVariableForm) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

def SlackVariableForm.isFeasible (P : SlackVariableForm) (x : Fin P.n → ℝ) : Prop :=
  x ∈ P.feasibleSet

def SlackVariableForm.objectiveValue (P : SlackVariableForm) (x : Fin P.n → ℝ) : ℝ :=
  P.objective x

def slackVariableForm : Set SlackVariableForm :=
  {P | ∃ x : Fin P.n → ℝ, P.isFeasible x}

def exercise13_9_b_linearProgram : SlackVariableForm where
  m := 2
  n := 4
  A := fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => 1
    | 0, 3 => 0
    | 1, 0 => 2
    | 1, 1 => (1 : ℝ) / 2
    | 1, 2 => 0
    | 1, 3 => 1
    | _, _ => 0
  b := fun i =>
    match i.1 with
    | 0 => 5
    | 1 => 8
    | _ => 0
  c := fun j =>
    match j.1 with
    | 0 => -5
    | 1 => -1
    | 2 => 0
    | 3 => 0
    | _ => 0

theorem exercise13_9_b_optimal_solution_and_value :
    exercise13_9_b_linearProgram.isFeasible (fun j =>
      match j.1 with
      | 0 => 4
      | 1 => 0
      | 2 => 1
      | 3 => 0
      | _ => 0) ∧
    exercise13_9_b_linearProgram.objectiveValue (fun j =>
      match j.1 with
      | 0 => 4
      | 1 => 0
      | 2 => 1
      | 3 => 0
      | _ => 0) = -20 ∧
    ∀ x : Fin exercise13_9_b_linearProgram.n → ℝ,
      exercise13_9_b_linearProgram.isFeasible x →
        -20 ≤ exercise13_9_b_linearProgram.objectiveValue x := by
  sorry

end «CAM-Bench-39»
