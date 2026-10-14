import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-349»

def IsMaximumLikelihoodEstimate {Y Θ : Type*} (p : Y → Θ → ℝ) (feasible : Set Θ) (y : Y) (θHat : Θ) : Prop :=
  θHat ∈ feasible ∧ ∀ θ ∈ feasible, p y θ ≤ p y θHat

structure MonotoneDeconvolutionLeastSquaresProblem where
  N : ℕ
  k : ℕ
  y : Fin (N + 1) → ℝ
  h : Fin k → ℝ

def MonotoneDeconvolutionLeastSquaresProblem.residual
    (p : MonotoneDeconvolutionLeastSquaresProblem) (x : Fin p.N → ℝ) (t : Fin p.N) : ℝ :=
  p.y t.succ - ∑ τ : Fin p.k, p.h τ * x ⟨t.1, t.2⟩

def MonotoneDeconvolutionLeastSquaresProblem.objective
    (p : MonotoneDeconvolutionLeastSquaresProblem) (x : Fin p.N → ℝ) : ℝ :=
  ∑ t : Fin p.N, (p.residual x t) ^ 2

def MonotoneDeconvolutionLeastSquaresProblem.IsFeasible
    (p : MonotoneDeconvolutionLeastSquaresProblem) (x : Fin p.N → ℝ) : Prop :=
  Monotone fun i j => x i ≤ x j

def MonotoneDeconvolutionLeastSquaresProblem.solutionSet
    (p : MonotoneDeconvolutionLeastSquaresProblem) : Set (Fin p.N → ℝ) :=
  {x | p.IsFeasible x}

def MonotoneDeconvolutionLeastSquaresProblem.IsOptimal
    (p : MonotoneDeconvolutionLeastSquaresProblem) (x : Fin p.N → ℝ) : Prop :=
  x ∈ p.solutionSet ∧ ∀ z ∈ p.solutionSet, p.objective x ≤ p.objective z

theorem monotoneDeconvolutionLeastSquares_mle_iff_leastSquares_optimal
    (p : MonotoneDeconvolutionLeastSquaresProblem)
    (hN : 1 ≤ p.N)
    (hk : 1 ≤ p.k)
    (xHat : Fin p.N → ℝ) :
    IsMaximumLikelihoodEstimate
      (fun y x => -((p.objective x) / 2))
      p.solutionSet
      p.y
      xHat ↔ p.IsOptimal xHat := by
  sorry

end «CAM-Bench-349»
