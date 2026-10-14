import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-38»

def IsSlackVariable {n : ℕ} (a x : Fin n → ℝ) (b s : ℝ) : Prop :=
  0 ≤ s ∧ (∑ i, a i * x i) + s = b

def originalFeasible13_9a (x : Fin 2 → ℝ) : Prop :=
  x 0 + x 1 ≤ 5 ∧
    2 * x 0 + (1 / 2 : ℝ) * x 1 ≤ 8 ∧
    0 ≤ x 0 ∧
    0 ≤ x 1

def originalObjective13_9a (x : Fin 2 → ℝ) : ℝ :=
  -5 * x 0 - x 1

def standardFeasible13_9a (xstd : Fin 4 → ℝ) : Prop :=
  xstd 0 + xstd 1 + xstd 2 = 5 ∧
    2 * xstd 0 + (1 / 2 : ℝ) * xstd 1 + xstd 3 = 8 ∧
    0 ≤ xstd 0 ∧ 0 ≤ xstd 1 ∧ 0 ≤ xstd 2 ∧ 0 ≤ xstd 3

def standardObjective13_9a (xstd : Fin 4 → ℝ) : ℝ :=
  -5 * xstd 0 - xstd 1

def standardLift13_9a (x : Fin 2 → ℝ) : Fin 4 → ℝ
  | 0 => x 0
  | 1 => x 1
  | 2 => 5 - (x 0 + x 1)
  | 3 => 8 - (2 * x 0 + (1 / 2 : ℝ) * x 1)

def standardProjection13_9a (xstd : Fin 4 → ℝ) : Fin 2 → ℝ
  | 0 => xstd 0
  | 1 => xstd 1

theorem linearProgramExercise13_9a_equiv_standardForm :
    (∀ x : Fin 2 → ℝ,
      originalFeasible13_9a x →
        standardFeasible13_9a (standardLift13_9a x) ∧
          standardProjection13_9a (standardLift13_9a x) = x ∧
          standardObjective13_9a (standardLift13_9a x) = originalObjective13_9a x) ∧
    (∀ xstd : Fin 4 → ℝ,
      standardFeasible13_9a xstd →
        originalFeasible13_9a (standardProjection13_9a xstd) ∧
          originalObjective13_9a (standardProjection13_9a xstd) =
            standardObjective13_9a xstd) := by
  sorry

end «CAM-Bench-38»
