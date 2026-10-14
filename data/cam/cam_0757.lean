import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-757»

structure NonlinearLeastSquaresProblem where
  n : ℕ
  m : ℕ
  residual : (Fin n → ℝ) → (Fin m → ℝ)

def NonlinearLeastSquaresProblem.objective
    (p : NonlinearLeastSquaresProblem) (x : Fin p.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (dotProduct (p.residual x) (p.residual x)) ^ 2

def NonlinearLeastSquaresProblem.gaussNewtonDirection
    (p : NonlinearLeastSquaresProblem) (J : (Fin p.n → ℝ) → Matrix (Fin p.m) (Fin p.n) ℝ)
    (x d : Fin p.n → ℝ) : Prop :=
  ((J x)ᵀ.mulVec ((J x).mulVec d)) = -((J x)ᵀ.mulVec (p.residual x))

def IsMinimumL2NormSolution {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (dhat : EuclideanSpace ℝ (Fin n)) : Prop :=
  dhat ∈ S ∧ ∀ d, d ∈ S → ‖dhat‖ ≤ ‖d‖

structure DifferentiableNonlinearLeastSquaresProblem extends NonlinearLeastSquaresProblem where
  jacobian : (Fin n → ℝ) → Matrix (Fin m) (Fin n) ℝ
  differentiableAt : ∀ x : Fin n → ℝ, DifferentiableAt ℝ residual x
  jacobian_spec : ∀ x : Fin n → ℝ,
    ∀ v : Fin n → ℝ,
      fderiv ℝ residual x v = (jacobian x).mulVec v

def DifferentiableNonlinearLeastSquaresProblem.gaussNewtonSystem
    (p : DifferentiableNonlinearLeastSquaresProblem) (x d : Fin p.n → ℝ) : Prop :=
  NonlinearLeastSquaresProblem.gaussNewtonDirection p.toNonlinearLeastSquaresProblem p.jacobian x d

open scoped Matrix

theorem gaussNewton_minimumL2NormSolution_of_fullRowRank
    (p : DifferentiableNonlinearLeastSquaresProblem) (x : EuclideanSpace ℝ (Fin p.n))
    (hmn : p.m ≤ p.n)
    (hInvertible : Invertible (p.jacobian x * (p.jacobian x)ᵀ)) :
    IsMinimumL2NormSolution
      {d : EuclideanSpace ℝ (Fin p.n) | p.gaussNewtonSystem x d}
      ((EuclideanSpace.equiv (Fin p.n) ℝ).symm
        (-((p.jacobian x)ᵀ).mulVec
          (((⅟ (p.jacobian x * (p.jacobian x)ᵀ)).mulVec (p.residual x))))) := by
  sorry

end «CAM-Bench-757»
