import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-65»

open scoped RealInnerProductSpace

structure BoxConstrainedProjectionProblem where
  n : ℕ
  xBar : EuclideanSpace ℝ (Fin n)
  l : Fin n → ℝ
  u : Fin n → ℝ
  bounds : ∀ i : Fin n, l i < u i

def BoxConstrainedProjectionProblem.feasibleSet
    (p : BoxConstrainedProjectionProblem) : Set (EuclideanSpace ℝ (Fin p.n)) :=
  {x | ∀ i : Fin p.n, p.l i ≤ x i ∧ x i ≤ p.u i}

def BoxConstrainedProjectionProblem.objective
    (p : BoxConstrainedProjectionProblem) (x : EuclideanSpace ℝ (Fin p.n)) : ℝ :=
  ‖x - p.xBar‖ ^ 2

def BoxConstrainedProjectionProblem.IsFeasible
    (p : BoxConstrainedProjectionProblem) (x : EuclideanSpace ℝ (Fin p.n)) : Prop :=
  x ∈ p.feasibleSet

def BoxConstrainedProjectionProblem.projection
    (p : BoxConstrainedProjectionProblem) : EuclideanSpace ℝ (Fin p.n) :=
  (WithLp.equiv 2 (Fin p.n → ℝ)).symm (fun i => max (p.l i) (min (p.xBar i) (p.u i)))

theorem box_constrained_projection_solution_eq_projection
    (p : BoxConstrainedProjectionProblem)
    (xStar : EuclideanSpace ℝ (Fin p.n))
    (hxStar_feasible : p.IsFeasible xStar)
    (hxStar_min :
      ∀ x : EuclideanSpace ℝ (Fin p.n), p.IsFeasible x → p.objective xStar ≤ p.objective x) :
    xStar = p.projection := by
  sorry

end «CAM-Bench-65»
