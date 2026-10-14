import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-751»

structure L1ResidualMinimization (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def L1ResidualMinimization.feasibleSet {m n : ℕ}
    (_p : L1ResidualMinimization m n) : Set (Fin n → ℝ) :=
  Set.univ

def L1ResidualMinimization.objectiveFun {m n : ℕ}
    (p : L1ResidualMinimization m n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, |(∑ j, p.A i j * x j) - p.b i|

def L1ResidualMinimization.residual {m n : ℕ} (p : L1ResidualMinimization m n) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  fun i => (∑ j, p.A i j * x j) - p.b i

def L1ResidualMinimization.is_feasible {m n : ℕ} (p : L1ResidualMinimization m n)
    (x : Fin n → ℝ) : Prop :=
  x ∈ p.feasibleSet

structure L1ResidualDualProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def L1ResidualDualProblem.feasibleSet {m n : ℕ}
    (p : L1ResidualDualProblem m n) : Set (Fin m → ℝ) :=
  {y | (∀ j, ∑ i, p.A i j * y i = 0) ∧ ∀ i, |y i| ≤ (1 : ℝ)}

def L1ResidualDualProblem.objectiveFun {m n : ℕ}
    (p : L1ResidualDualProblem m n) (y : Fin m → ℝ) : ℝ :=
  -∑ i, p.b i * y i

def L1ResidualDualProblem.objective {m n : ℕ} (p : L1ResidualDualProblem m n)
    (y : Fin m → ℝ) : ℝ :=
  p.objectiveFun y

def L1ResidualDualProblem.is_feasible {m n : ℕ} (p : L1ResidualDualProblem m n)
    (y : Fin m → ℝ) : Prop :=
  y ∈ p.feasibleSet

theorem l1_residual_minimization_dual_is_linf_constrained
    (m n : ℕ)
    (p : L1ResidualMinimization m n) :
    let d : L1ResidualDualProblem m n := {
      A := p.A
      b := p.b
    }
    d.A = p.A ∧
    d.b = p.b ∧
    (∀ y : Fin m → ℝ, d.objective y = -∑ i, p.b i * y i) ∧
    (∀ y : Fin m → ℝ,
      d.is_feasible y ↔ (∀ j, ∑ i, p.A i j * y i = 0) ∧ ∀ i, |y i| ≤ (1 : ℝ)) := by
  sorry

end «CAM-Bench-751»
