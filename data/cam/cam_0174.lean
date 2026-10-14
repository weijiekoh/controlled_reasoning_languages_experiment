import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-174»

structure HasLowRankPlusDiagonalStructure (n k : ℕ) where
  M : Matrix (Fin n) (Fin n) ℝ
  U : Matrix (Fin n) (Fin k) ℝ
  V : Matrix (Fin n) (Fin k) ℝ
  D : Matrix (Fin n) (Fin n) ℝ
  decomp_eq : M = U * V.transpose + D
  diagonal_D : D.IsDiag

structure QuadraticPortfolioOptimization (n : ℕ) where
  mu : Fin n → ℝ
  Sigma : Matrix (Fin n) (Fin n) ℝ
  sigma_symm : Sigma.transpose = Sigma
  sigma_pos_def : Sigma.PosDef

def QuadraticPortfolioOptimization.feasible
    {n : ℕ} (p : QuadraticPortfolioOptimization n) (w : Fin n → ℝ) : Prop :=
  ∑ i : Fin n, w i = 1

def QuadraticPortfolioOptimization.objective
    {n : ℕ} (p : QuadraticPortfolioOptimization n) (w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, p.mu i * w i
    - (1 / 2 : ℝ) * ∑ i : Fin n, w i * ∑ j : Fin n, p.Sigma i j * w j

theorem dense_kkt_portfolio_flop_count_theta_n_cubed
    (n k : ℕ) (p : QuadraticPortfolioOptimization n)
    (hstruct : HasLowRankPlusDiagonalStructure n k)
    (hSigma : p.Sigma = hstruct.M) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ N : ℕ, 1 ≤ N →
        c₁ * (N : ℝ)^3 ≤ ((N + 1 : ℕ) : ℝ)^3 ∧
        (((N + 1 : ℕ) : ℝ)^3 ≤ c₂ * (N : ℝ)^3) := by
  sorry

end «CAM-Bench-174»
