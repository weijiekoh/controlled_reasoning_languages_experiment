import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-176»

open scoped BigOperators

structure WorstCaseVariancePortfolioProblem (n : ℕ) where
  μ : Fin n → ℝ
  Sigma : Matrix (Fin n) (Fin n) ℝ
  R : ℝ
  Rwc : ℝ

def WorstCaseVariancePortfolioProblem.objective {n : ℕ}
    (p : WorstCaseVariancePortfolioProblem n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, p.μ i * x i

def WorstCaseVariancePortfolioProblem.quadraticRisk {n : ℕ}
    (p : WorstCaseVariancePortfolioProblem n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * p.Sigma i j * x j

def WorstCaseVariancePortfolioProblem.worstCaseRisk {n : ℕ}
    (p : WorstCaseVariancePortfolioProblem n) (x : Fin n → ℝ) : ℝ :=
  (∑ i, Real.sqrt (p.Sigma i i) * |x i|) ^ 2

def WorstCaseVariancePortfolioProblem.IsFeasible {n : ℕ}
    (p : WorstCaseVariancePortfolioProblem n) (x : Fin n → ℝ) : Prop :=
  p.quadraticRisk x ≤ p.R ∧ p.worstCaseRisk x ≤ p.Rwc

def WorstCaseVariancePortfolioProblem.IsWorstCaseFeasible {n : ℕ}
    (p : WorstCaseVariancePortfolioProblem n) (x : Fin n → ℝ) : Prop :=
  p.worstCaseRisk x ≤ p.Rwc

theorem worstCaseVariancePortfolioProblem_worstCaseRisk_sufficient
    (n : ℕ)
    (p : WorstCaseVariancePortfolioProblem n)
    (hR : 0 < p.R)
    (hRwc : p.R < p.Rwc)
    (hrisk_dom :
      ∀ x : Fin n → ℝ,
        p.IsWorstCaseFeasible x → p.quadraticRisk x ≤ p.R) :
    ∀ x : Fin n → ℝ, p.IsWorstCaseFeasible x → p.IsFeasible x := by
  sorry

end «CAM-Bench-176»
