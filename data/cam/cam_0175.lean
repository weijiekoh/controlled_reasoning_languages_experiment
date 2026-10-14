import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-175»

open scoped BigOperators

structure EquivalentConvexOptimizationProblem where
  n : ℕ
  l : Fin n → ℝ
  u : Fin n → ℝ
  Sigma : Matrix (Fin n) (Fin n) ℝ
  sigmaMax : ℝ

def EquivalentConvexOptimizationProblem.isFeasible
    (P : EquivalentConvexOptimizationProblem)
    (x y : Fin P.n → ℝ) : Prop :=
  (∑ i, x i) = 1 ∧
  dotProduct x (fun i => ∑ j, P.Sigma i j * x j) ≤ P.sigmaMax ^ 2 ∧
  (∀ i, 0 ≤ y i) ∧
  (∀ i, 0 ≤ y i + x i)

def EquivalentConvexOptimizationProblem.objective
    (P : EquivalentConvexOptimizationProblem)
    (x y : Fin P.n → ℝ) : ℝ :=
  (∑ i, P.l i * x i) - ∑ i, (P.u i - P.l i) * y i

theorem worstCaseReturn_maximization_equivalent_to_equivalent_convex_optimization
    (P : EquivalentConvexOptimizationProblem)
    (hlu : ∀ i, P.l i ≤ P.u i) :
    ∀ x : Fin P.n → ℝ,
      (∑ i, x i = 1 ∧
        dotProduct x (fun i => ∑ j, P.Sigma i j * x j) ≤ P.sigmaMax ^ 2) →
      ∃ y : Fin P.n → ℝ,
        P.isFeasible x y ∧
        P.objective x y = ∑ i, min (P.l i * x i) (P.u i * x i) := by
  sorry

end «CAM-Bench-175»
