import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-750»

structure L1NormMinimizationProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def L1NormMinimizationProblem.objective
    {m n : ℕ} (_P : L1NormMinimizationProblem m n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i|

def L1NormMinimizationProblem.feasibleSet
    {m n : ℕ} (P : L1NormMinimizationProblem m n) : Set (Fin n → ℝ) :=
  {x | P.A.mulVec x = P.b}

def L1NormMinimizationProblem.isFeasible
    {m n : ℕ} (P : L1NormMinimizationProblem m n) (x : Fin n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def L1NormMinimizationProblem.dualFeasible
    {m n : ℕ} (P : L1NormMinimizationProblem m n) (y : Fin m → ℝ) : Prop :=
  ∀ j : Fin n, |(P.A.transpose.mulVec y) j| ≤ 1

def L1NormMinimizationProblem.dualObjective
    {m n : ℕ} (P : L1NormMinimizationProblem m n) (y : Fin m → ℝ) : ℝ :=
  ∑ i, P.b i * y i

theorem l1NormMinimization_weak_duality
    {m n : ℕ} (P : L1NormMinimizationProblem m n) :
    ∀ x : Fin n → ℝ, ∀ y : Fin m → ℝ,
      P.isFeasible x → P.dualFeasible y →
        P.dualObjective y ≤ P.objective x := by
  sorry

end «CAM-Bench-750»
