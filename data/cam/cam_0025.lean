import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-25»

def IsFeasiblePoint {α β : Type*} [Zero β] (c : α → β) (x : α) : Prop :=
  c x = 0

def IsGlobalSolution {α : Type _} {β : Type _} [LE β] (f : α → β) (feasible : α → Prop)
    (xStar : α) : Prop :=
  feasible xStar ∧ ∀ x, feasible x → f xStar ≤ f x

def IsStrictLocalSolution (f : ℝ → ℝ) (feasible : ℝ → Prop) (xStar : ℝ) : Prop :=
  feasible xStar ∧ ∃ δ > 0, ∀ x : ℝ, feasible x → x ≠ xStar → |x - xStar| < δ → f xStar < f x

def IsIsolatedLocalSolution (feasible : ℝ → Prop) (xStar : ℝ) : Prop :=
  feasible xStar ∧ ∃ δ > 0, ∀ x : ℝ, feasible x → |x - xStar| < δ → x = xStar

structure ScalarEqualityConstrainedProblem where
  objective : ℝ → ℝ
  constraint : ℝ → ℝ

def ScalarEqualityConstrainedProblem.standard : ScalarEqualityConstrainedProblem where
  objective := fun x => x ^ 2
  constraint := fun x => if x = 0 then 0 else x ^ 6 * Real.sin (1 / x)

def ScalarEqualityConstrainedProblem.is_feasible (p : ScalarEqualityConstrainedProblem) (x : ℝ) : Prop :=
  IsFeasiblePoint p.constraint x

def ScalarEqualityConstrainedProblem.objective_value (p : ScalarEqualityConstrainedProblem) (x : ℝ) : ℝ :=
  p.objective x

theorem zero_is_global_and_strict_local_but_not_isolated_local_solution :
    let p := ScalarEqualityConstrainedProblem.standard
    IsGlobalSolution p.objective (ScalarEqualityConstrainedProblem.is_feasible p) 0 ∧
      IsStrictLocalSolution p.objective (ScalarEqualityConstrainedProblem.is_feasible p) 0 ∧
        ¬ IsIsolatedLocalSolution (ScalarEqualityConstrainedProblem.is_feasible p) 0 := by
  sorry

end «CAM-Bench-25»
