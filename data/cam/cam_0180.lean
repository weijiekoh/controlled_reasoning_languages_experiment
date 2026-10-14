import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-180»

open Matrix

structure RobustMeanVariancePortfolioProblem where
  n : ℕ
  M : ℕ
  hM : 1 ≤ M
  μ : Fin n → ℝ
  γ : ℝ
  hγ : 0 < γ
  Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : ∀ k : Fin M, (Sigma k).IsSymm
  Sigma_pos : ∀ k : Fin M, PosDef (Sigma k)
  wStar : Fin n → ℝ

def RobustMeanVariancePortfolioProblem.isFeasible
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, w i) = 1

def RobustMeanVariancePortfolioProblem.objective
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : ℝ :=
  (∑ i : Fin P.n, P.μ i * w i) -
    P.γ * sSup (Set.range fun k : Fin P.M => dotProduct w (P.Sigma k *ᵥ w))

def RobustMeanVariancePortfolioProblem.isOptimal
    (P : RobustMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  P.isFeasible w ∧ ∀ z : Fin P.n → ℝ, P.isFeasible z → P.objective z ≤ P.objective w

structure WeightedMeanVariancePortfolioProblem where
  n : ℕ
  M : ℕ
  hM : 1 ≤ M
  μ : Fin n → ℝ
  γ : Fin M → ℝ
  hγ : ∀ k : Fin M, 0 < γ k
  Sigma : Fin M → Matrix (Fin n) (Fin n) ℝ
  Sigma_symm : ∀ k : Fin M, (Sigma k).IsSymm
  Sigma_pos : ∀ k : Fin M, PosDef (Sigma k)

def WeightedMeanVariancePortfolioProblem.objective
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : ℝ :=
  (∑ i : Fin P.n, P.μ i * w i) -
    ∑ k : Fin P.M, P.γ k * dotProduct w (P.Sigma k *ᵥ w)

def WeightedMeanVariancePortfolioProblem.isFeasible
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, w i) = 1

def WeightedMeanVariancePortfolioProblem.isOptimalSolution
    (P : WeightedMeanVariancePortfolioProblem) (w : Fin P.n → ℝ) : Prop :=
  P.isFeasible w ∧ ∀ z : Fin P.n → ℝ, P.isFeasible z → P.objective z ≤ P.objective w

theorem robust_optimal_implies_weighted_optimal
    (P : RobustMeanVariancePortfolioProblem)
    (hPopt : P.isOptimal P.wStar) :
    ∃ γw : Fin P.M → ℝ,
      ∃ hγw : ∀ k : Fin P.M, 0 ≤ γw k,
        (∑ k : Fin P.M, γw k) = P.γ ∧
        ((∑ i : Fin P.n, P.wStar i) = 1 ∧
          ∀ z : Fin P.n → ℝ, (∑ i : Fin P.n, z i) = 1 →
            ((∑ i : Fin P.n, P.μ i * z i) -
                ∑ k : Fin P.M, γw k * dotProduct z (P.Sigma k *ᵥ z)) ≤
              ((∑ i : Fin P.n, P.μ i * P.wStar i) -
                ∑ k : Fin P.M, γw k * dotProduct P.wStar (P.Sigma k *ᵥ P.wStar))) := by
  sorry

end «CAM-Bench-180»
