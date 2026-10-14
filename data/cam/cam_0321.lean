import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-321»

def IsOptimalSolution {α β : Type*} [Preorder β] (S : Set α) (f : α → β) (xStar : α) : Prop :=
  xStar ∈ S ∧ ∀ x ∈ S, f xStar ≤ f x

structure LeastSquaresL1RegularizationProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  γ : ℝ
  gamma_pos : 0 < γ

def LeastSquaresL1RegularizationProblem.objective
    {m n : ℕ} (p : LeastSquaresL1RegularizationProblem m n) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct (p.A.mulVec x - p.b) (p.A.mulVec x - p.b)) +
    p.γ * ∑ i, |x i|

def LeastSquaresL1RegularizationProblem.isOptimal
    {m n : ℕ} (p : LeastSquaresL1RegularizationProblem m n) (xStar : Fin n → ℝ) : Prop :=
  IsOptimalSolution Set.univ p.objective xStar

theorem optimality_conditions_of_leastSquaresL1Regularization
    {m n : ℕ} (p : LeastSquaresL1RegularizationProblem m n) (xStar : Fin n → ℝ)
    (hxOpt : p.isOptimal xStar)
    (hres : p.A.mulVec xStar - p.b ≠ 0) :
    let r : Fin m → ℝ :=
      (Real.sqrt (dotProduct (p.A.mulVec xStar - p.b) (p.A.mulVec xStar - p.b)))⁻¹ •
        (p.A.mulVec xStar - p.b)
    (∀ i, |(p.Aᵀ.mulVec r) i| ≤ p.γ) ∧
      (dotProduct r (p.A.mulVec xStar) + p.γ * ∑ i, |xStar i| = 0) := by
  sorry

end «CAM-Bench-321»
