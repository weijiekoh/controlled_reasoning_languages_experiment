import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-749»

def IsSingularValueDecomposition
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq m] [DecidableEq n] [DecidableEq r]
    (Y : Matrix m n ℝ) (U : Matrix m r ℝ) (Sigma : Matrix r r ℝ) (V : Matrix n r ℝ) : Prop :=
  Y = U * Sigma * Vᵀ ∧
  Uᵀ * U = 1 ∧
  Vᵀ * V = 1 ∧
  Fintype.card r = Matrix.rank Y ∧
  (∀ i j : r, i ≠ j → Sigma i j = 0) ∧
  ∀ i : r, 0 ≤ Sigma i i

def IsNuclearNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (nu : Matrix m n ℝ → ℝ) : Prop :=
  ∀ {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix m n ℝ) (U : Matrix m r ℝ) (Sigma : Matrix r r ℝ) (V : Matrix n r ℝ),
    IsSingularValueDecomposition X U Sigma V → nu X = ∑ i : r, Sigma i i

def frobeniusDistanceSquared
    {m n : Type*} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (X i j - Y i j) ^ 2

structure NuclearNormProximalProblem
    (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] where
  Y : Matrix m n ℝ
  nuclearNorm : Matrix m n ℝ → ℝ
  isNuclearNorm : IsNuclearNorm nuclearNorm

def NuclearNormProximalProblem.objective
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : NuclearNormProximalProblem m n) (X : Matrix m n ℝ) : ℝ :=
  P.nuclearNorm X + (1 / 2 : ℝ) * frobeniusDistanceSquared X P.Y

def NuclearNormProximalProblem.positivePart (a : ℝ) : ℝ :=
  max a 0

def NuclearNormProximalProblem.isMinimizer
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : NuclearNormProximalProblem m n) (X : Matrix m n ℝ) : Prop :=
  ∀ Z : Matrix m n ℝ, P.objective X ≤ P.objective Z

theorem nuclearNormProximalProblem_has_soft_thresholding_solution
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq m] [DecidableEq n] [DecidableEq r]
    (P : NuclearNormProximalProblem m n)
    (U : Matrix m r ℝ) (Sigma : Matrix r r ℝ) (V : Matrix n r ℝ)
    (hsvd : IsSingularValueDecomposition P.Y U Sigma V) :
    P.isMinimizer
      (U *
        (Matrix.diagonal fun i => NuclearNormProximalProblem.positivePart (Sigma i i - 1)) *
        Vᵀ) := by
  sorry

end «CAM-Bench-749»
