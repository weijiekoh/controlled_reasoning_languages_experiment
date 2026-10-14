import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-405»

structure EqualityConstrainedOptimizationProblem (n p : ℕ) where
  objective : (Fin n → ℝ) → ℝ
  constraintVectors : Fin p → (Fin n → ℝ)
  constraintConstants : Fin p → ℝ

def EqualityConstrainedOptimizationProblem.isFeasible
    {n p : ℕ} (P : EqualityConstrainedOptimizationProblem n p) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin p, ∑ j : Fin n, P.constraintVectors i j * x j = P.constraintConstants i

def EqualityConstrainedOptimizationProblem.feasibleSet
    {n p : ℕ} (P : EqualityConstrainedOptimizationProblem n p) : Set (Fin n → ℝ) :=
  {x | P.isFeasible x}

def EqualityConstrainedOptimizationProblem.objectiveValue
    {n p : ℕ} (P : EqualityConstrainedOptimizationProblem n p) (x : Fin n → ℝ) : ℝ :=
  P.objective x

def IsInfeasibleStartNewtonIterates
    {n p : ℕ} (P : EqualityConstrainedOptimizationProblem n p)
    (newtonIterates : ℕ → (Fin n → ℝ)) : Prop :=
  ∀ k : ℕ,
    ∃ Δx : Fin n → ℝ,
      newtonIterates (k + 1) = newtonIterates k + Δx ∧
      (∀ i : Fin p,
        ∑ j : Fin n, P.constraintVectors i j * Δx j =
          P.constraintConstants i -
            ∑ j : Fin n, P.constraintVectors i j * newtonIterates k j)

theorem infeasibleStartNewton_feasibility_preserved
    {n p : ℕ} (P : EqualityConstrainedOptimizationProblem n p)
    (newtonIterates : ℕ → (Fin n → ℝ))
    (hNewton : IsInfeasibleStartNewtonIterates P newtonIterates)
    (h0 : P.isFeasible (newtonIterates 0)) :
    ∀ k : ℕ, P.isFeasible (newtonIterates k) := by
  sorry

end «CAM-Bench-405»
