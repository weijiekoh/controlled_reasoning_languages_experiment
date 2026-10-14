import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-587»

open scoped BigOperators

structure MinimumCostFlowLP where
  n : ℕ
  c : Fin n → Fin n → ℝ
  b : Fin n → ℝ
  l : Fin n → Fin n → ℝ
  u : Fin n → Fin n → ℝ

def MinimumCostFlowLP.objective (p : MinimumCostFlowLP) (x : Fin p.n → Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.n, ∑ j : Fin p.n, p.c i j * x i j

def MinimumCostFlowLP.flowConservation (p : MinimumCostFlowLP) (x : Fin p.n → Fin p.n → ℝ) : Prop :=
  ∀ i : Fin p.n, (∑ j : Fin p.n, x j i) + p.b i - ∑ j : Fin p.n, x i j = 0

def MinimumCostFlowLP.boxConstraints (p : MinimumCostFlowLP) (x : Fin p.n → Fin p.n → ℝ) : Prop :=
  ∀ i : Fin p.n, ∀ j : Fin p.n, p.l i j ≤ x i j ∧ x i j ≤ p.u i j

def MinimumCostFlowLP.IsFeasible (p : MinimumCostFlowLP) (x : Fin p.n → Fin p.n → ℝ) : Prop :=
  p.flowConservation x ∧ p.boxConstraints x

theorem minimumCostFlowLP_feasible_set_convex_and_objective_affine
    (p : MinimumCostFlowLP) :
    Convex ℝ {x : Fin p.n → Fin p.n → ℝ | p.IsFeasible x} ∧
    ∀ x y : Fin p.n → Fin p.n → ℝ,
      p.IsFeasible x →
      p.IsFeasible y →
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        p.objective (θ • x + (1 - θ) • y) =
          θ * p.objective x + (1 - θ) * p.objective y := by
  sorry

end «CAM-Bench-587»
