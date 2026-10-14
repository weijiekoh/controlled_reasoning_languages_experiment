import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-747»

def IsMoorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (X : Matrix n m ℝ) : Prop :=
  (A * X * A = A ∧
    X * A * X = X ∧
    (A * X)ᵀ = A * X ∧
    (X * A)ᵀ = X * A) ∧
    ∀ Y : Matrix n m ℝ,
      (A * Y * A = A ∧
        Y * A * Y = Y ∧
        (A * Y)ᵀ = A * Y ∧
        (Y * A)ᵀ = Y * A) → Y = X

def moorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : Matrix n m ℝ :=
  by
    classical
    exact
      if h : ∃ X : Matrix n m ℝ, IsMoorePenrosePseudoinverse A X then
        Classical.choose h
      else
        0

structure MinimumEuclideanNormProblem (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] where
  A : Matrix m n ℝ
  b : m → ℝ

def MinimumEuclideanNormProblem.isFeasible {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (P : MinimumEuclideanNormProblem m n) (x : n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def MinimumEuclideanNormProblem.objective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (P : MinimumEuclideanNormProblem m n) (x : n → ℝ) : ℝ :=
  ‖x‖

def MinimumEuclideanNormProblem.solutionSet {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (P : MinimumEuclideanNormProblem m n) : Set (n → ℝ) :=
  {x | P.isFeasible x ∧ ∀ y, P.isFeasible y → P.objective x ≤ P.objective y}

theorem minimumEuclideanNormProblem_solution_eq_pseudoinverse_mul
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) (X : Matrix n m ℝ)
    (hMP : X = moorePenrosePseudoinverse A)
    (hfeas : ∃ x : n → ℝ, A.mulVec x = b) :
    X.mulVec b ∈ (MinimumEuclideanNormProblem.solutionSet
      { A := A, b := b } : Set (n → ℝ)) := by
  sorry

end «CAM-Bench-747»
