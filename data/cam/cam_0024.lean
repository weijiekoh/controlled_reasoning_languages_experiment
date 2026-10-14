import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-24»

def IsFeasible {α : Type _} (c : α → ℝ) (x : α) : Prop := c x = 0

def IsIsolatedLocalSolution {α : Type _} [TopologicalSpace α] (c : α → ℝ) (xbar : α) : Prop :=
  IsFeasible c xbar ∧ ∃ N : Set α, IsOpen N ∧ xbar ∈ N ∧ ∀ x ∈ N, IsFeasible c x → x = xbar

structure ScalarEqualityConstrainedProblem where
  objective : ℝ → ℝ
  constraint : ℝ → ℝ

def ScalarEqualityConstrainedProblem.example : ScalarEqualityConstrainedProblem where
  objective := fun x => x ^ 2
  constraint := fun x => if x = 0 then 0 else x ^ 6 * Real.sin (1 / x)

def ScalarEqualityConstrainedProblem.isFeasible
    (p : ScalarEqualityConstrainedProblem) (x : ℝ) : Prop :=
  IsFeasible p.constraint x

def ScalarEqualityConstrainedProblem.objectiveValue
    (p : ScalarEqualityConstrainedProblem) (x : ℝ) : ℝ :=
  p.objective x

theorem every_nonzero_feasible_point_is_isolated_local_solution
    (xbar : ℝ)
    (hxbar_ne : xbar ≠ 0)
    (hfeas : ScalarEqualityConstrainedProblem.isFeasible ScalarEqualityConstrainedProblem.example xbar) :
    IsIsolatedLocalSolution ScalarEqualityConstrainedProblem.example.constraint xbar := by
  sorry

end «CAM-Bench-24»
