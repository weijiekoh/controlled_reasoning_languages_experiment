import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-179»

open scoped BigOperators

structure MeanVariancePortfolioProblem where
  n : ℕ
  T : ℕ
  h : Fin T → Fin n → ℝ
  h_pos : ∀ t : Fin T, (∑ i : Fin n, h t i) > 0
  μ : Fin n → ℝ
  Sigma : Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : Sigma.IsSymm
  Sigma_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Sigma.mulVec x)
  γ : ℝ
  γ_pos : 0 < γ

def MeanVariancePortfolioProblem.normalizedWeight (p : MeanVariancePortfolioProblem) (t : Fin p.T) :
    Fin p.n → ℝ :=
  fun i => p.h t i / (∑ j : Fin p.n, p.h t j)

def MeanVariancePortfolioProblem.objective (p : MeanVariancePortfolioProblem) (w : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.n, p.μ i * w i
    - (1 / 2 : ℝ) * p.γ * dotProduct w (p.Sigma.mulVec w)

def MeanVariancePortfolioProblem.feasible (p : MeanVariancePortfolioProblem) (w : Fin p.n → ℝ) : Prop :=
  (∑ i : Fin p.n, w i) = 1

def MeanVariancePortfolioProblem.IsSolution (p : MeanVariancePortfolioProblem) (wStar : Fin p.n → ℝ) :
    Prop :=
  p.feasible wStar ∧ ∀ w : Fin p.n → ℝ, p.feasible w → p.objective w ≤ p.objective wStar

structure PortfolioRebalancingProblem where
  base : MeanVariancePortfolioProblem
  t : Fin base.T
  κ : Fin base.n → ℝ
  κ_nonneg : ∀ i : Fin base.n, 0 ≤ κ i
  w_tilde : Fin base.n → ℝ

def PortfolioRebalancingProblem.transactionCost
    (p : PortfolioRebalancingProblem) (w : Fin p.base.n → ℝ) : ℝ :=
  ∑ i : Fin p.base.n, p.κ i * |w i - p.base.normalizedWeight p.t i|

def PortfolioRebalancingProblem.objective
    (p : PortfolioRebalancingProblem) (w : Fin p.base.n → ℝ) : ℝ :=
  ∑ i : Fin p.base.n, p.base.μ i * w i
    - (1 / 2 : ℝ) * dotProduct w (p.base.Sigma.mulVec w)
    - p.transactionCost w

def PortfolioRebalancingProblem.feasibleSet
    (p : PortfolioRebalancingProblem) (w : Fin p.base.n → ℝ) : Prop :=
  (∑ i : Fin p.base.n, w i) = 1

def PortfolioRebalancingProblem.IsSolution
    (p : PortfolioRebalancingProblem) (wStar : Fin p.base.n → ℝ) : Prop :=
  p.feasibleSet wStar ∧
    ∀ w : Fin p.base.n → ℝ, p.feasibleSet w → p.objective w ≤ p.objective wStar

theorem rebalancing_self_optimal_of_componentwise_transaction_bound
    (p : MeanVariancePortfolioProblem)
    (t : Fin p.T)
    (wStar : Fin p.n → ℝ)
    (hwStar : p.IsSolution wStar)
    (κ : Fin p.n → ℝ)
    (hκ_nonneg : ∀ i : Fin p.n, 0 ≤ κ i)
    (hκ : ∀ i : Fin p.n, p.γ * |(p.Sigma.mulVec (p.normalizedWeight t - wStar)) i| ≤ κ i) :
    let objective : (Fin p.n → ℝ) → ℝ :=
      fun w =>
        ∑ i : Fin p.n, p.μ i * w i
          - (1 / 2 : ℝ) * p.γ * dotProduct w (p.Sigma.mulVec w)
          - ∑ i : Fin p.n, κ i * |w i - p.normalizedWeight t i|
    let feasible : (Fin p.n → ℝ) → Prop :=
      fun w => (∑ i : Fin p.n, w i) = 1
    feasible (p.normalizedWeight t) ∧
      ∀ w : Fin p.n → ℝ, feasible w → objective w ≤ objective (p.normalizedWeight t) := by
  sorry

end «CAM-Bench-179»
