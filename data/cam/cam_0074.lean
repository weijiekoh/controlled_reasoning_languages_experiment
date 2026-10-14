import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-74»

def quadraticPenaltyFunction {α ι : Type _} [Fintype ι] (f : α → ℝ) (h : ι → α → ℝ)
    (μ : ℝ) (x : α) : ℝ :=
  f x + (1 / (2 * μ)) * ∑ i, (h i x) ^ 2

structure EqualityConstrainedQuadraticProgram where
  x : Fin 2 → ℝ

def EqualityConstrainedQuadraticProgram.objective (p : EqualityConstrainedQuadraticProgram) : ℝ :=
  -5 * (p.x 0) ^ 2 + (p.x 1) ^ 2

def EqualityConstrainedQuadraticProgram.constraintFunction : Fin 1 → (Fin 2 → ℝ) → ℝ :=
  fun _ x => x 0 - 1

def EqualityConstrainedQuadraticProgram.is_feasible
    (x : Fin 2 → ℝ) : Prop :=
  x 0 = 1

def EqualityConstrainedQuadraticProgram.penaltyObjective
    (μ : ℝ) : EqualityConstrainedQuadraticProgram → ℝ :=
  fun p => quadraticPenaltyFunction
    (fun x : Fin 2 → ℝ => -5 * (x 0) ^ 2 + (x 1) ^ 2)
    EqualityConstrainedQuadraticProgram.constraintFunction
    μ
    p.x

theorem stationary_points_of_penaltyObjective_mu_one :
    {x : Fin 2 → ℝ |
      let Q := quadraticPenaltyFunction
        (fun y : Fin 2 → ℝ => -5 * (y 0) ^ 2 + (y 1) ^ 2)
        EqualityConstrainedQuadraticProgram.constraintFunction
        1
      (fderiv ℝ Q x) (Pi.single 0 (1 : ℝ)) = 0 ∧
      (fderiv ℝ Q x) (Pi.single 1 (1 : ℝ)) = 0} =
    {x : Fin 2 → ℝ | x 0 = -1 / 9 ∧ x 1 = 0} := by
  sorry

end «CAM-Bench-74»
