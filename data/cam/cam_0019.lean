import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-19»

structure QuadraticEqualityConstrainedProblem where
  objective : ℝ × ℝ → ℝ
  constraint : ℝ × ℝ → ℝ

def QuadraticEqualityConstrainedProblem.feasibleSet
    (P : QuadraticEqualityConstrainedProblem) : Set (ℝ × ℝ) :=
  {p | P.constraint p = 0}

def QuadraticEqualityConstrainedProblem.isFeasible
    (P : QuadraticEqualityConstrainedProblem) (p : ℝ × ℝ) : Prop :=
  p ∈ P.feasibleSet

def QuadraticEqualityConstrainedProblem.standard :
    QuadraticEqualityConstrainedProblem where
  objective := fun p => (p.1 - 1) ^ 2 + (p.2 - 2) ^ 2
  constraint := fun p => (p.1 - 1) ^ 2 - 5 * p.2

def QuadraticEqualityConstrainedProblem.objectiveValue
    (P : QuadraticEqualityConstrainedProblem) (p : ℝ × ℝ) : ℝ :=
  P.objective p

theorem quadraticEqualityConstrainedProblem_solution_points :
    {p : ℝ × ℝ |
        QuadraticEqualityConstrainedProblem.standard.isFeasible p ∧
        ∀ q : ℝ × ℝ,
          QuadraticEqualityConstrainedProblem.standard.isFeasible q →
            QuadraticEqualityConstrainedProblem.standard.objectiveValue p ≤
              QuadraticEqualityConstrainedProblem.standard.objectiveValue q} =
      {(1, 0)} := by
  sorry

end «CAM-Bench-19»
