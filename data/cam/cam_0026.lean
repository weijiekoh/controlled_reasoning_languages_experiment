import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-26»

def IsIsolatedLocalSolution {α : Type*} [PseudoMetricSpace α] (X : Set α) (f : α → ℝ) (xstar : α) : Prop :=
  IsLocalMinOn f X xstar ∧ ∃ r > 0, ∀ y ∈ X, dist y xstar < r → IsLocalMinOn f X y → y = xstar

def IsStrictLocalSolution {α : Type*} [PseudoMetricSpace α] (X : Set α) (f : α → ℝ) (xstar : α) : Prop :=
  xstar ∈ X ∧ ∃ r > 0, ∀ x ∈ X, dist x xstar < r → x ≠ xstar → f xstar < f x

theorem isolatedLocalSolution_not_necessarily_strict :
    ¬ ∀ {α : Type*} [PseudoMetricSpace α] (X : Set α) (f : α → ℝ) (xstar : α),
      IsIsolatedLocalSolution X f xstar → IsStrictLocalSolution X f xstar := by
  sorry

end «CAM-Bench-26»
