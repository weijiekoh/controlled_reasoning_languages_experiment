import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-82»

structure LeastSquaresTrustRegionProblem where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  c : Fin m → ℝ
  Δ : ℝ

def LeastSquaresTrustRegionProblem.residual (p : LeastSquaresTrustRegionProblem) (v : Fin p.n → ℝ) :
    Fin p.m → ℝ :=
  fun i => (∑ j, p.A i j * v j) + p.c i

def LeastSquaresTrustRegionProblem.objective
    (p : LeastSquaresTrustRegionProblem) (v : Fin p.n → ℝ) : ℝ :=
  dotProduct (p.residual v) (p.residual v)

def LeastSquaresTrustRegionProblem.feasibleSet
    (p : LeastSquaresTrustRegionProblem) : Set (Fin p.n → ℝ) :=
  {v | Real.sqrt (dotProduct v v) ≤ (0.8 : ℝ) * p.Δ}

def LeastSquaresTrustRegionProblem.transposeRange
    (p : LeastSquaresTrustRegionProblem) : Set (Fin p.n → ℝ) :=
  Set.range p.A.transpose.mulVec

theorem exists_solution_in_transposeRange (p : LeastSquaresTrustRegionProblem)
    (hΔ : 0 ≤ p.Δ) :
    ∃ v : Fin p.n → ℝ,
      v ∈ p.feasibleSet ∧
      v ∈ p.transposeRange ∧
      ∀ w : Fin p.n → ℝ, w ∈ p.feasibleSet → p.objective v ≤ p.objective w := by
  sorry

end «CAM-Bench-82»
