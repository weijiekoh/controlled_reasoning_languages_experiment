import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-23»

def IsFeasiblePoint {α : Type _} (c : α → ℝ) (x : α) : Prop := c x = 0

def ScalarEqualityConstrainedProblem : (ℝ → ℝ) × (ℝ → ℝ) :=
  (fun x => x^2, fun x => if x = 0 then 0 else x^6 * Real.sin (1 / x))

def scalarOscillatoryConstraint (x : ℝ) : ℝ :=
  if x = 0 then 0 else x^6 * Real.sin (1 / x)

def ScalarEqualityConstrainedProblem.isFeasible (p : (ℝ → ℝ) × (ℝ → ℝ)) (x : ℝ) : Prop :=
  p.2 x = 0

def ScalarEqualityConstrainedProblem.objectiveValue (p : (ℝ → ℝ) × (ℝ → ℝ)) (x : ℝ) : ℝ :=
  p.1 x

def exercise12_1aProblem : (ℝ → ℝ) × (ℝ → ℝ) :=
  ScalarEqualityConstrainedProblem

theorem scalarOscillatoryConstraint_c2_and_feasible_points_characterization :
    ContDiff ℝ 2 scalarOscillatoryConstraint ∧
      ∀ x : ℝ,
        ScalarEqualityConstrainedProblem.isFeasible exercise12_1aProblem x ↔
          x = 0 ∨ ∃ k : ℤ, k ≠ 0 ∧ x = 1 / ((k : ℝ) * Real.pi) := by
  sorry

end «CAM-Bench-23»
