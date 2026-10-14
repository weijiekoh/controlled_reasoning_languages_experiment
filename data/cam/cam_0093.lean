import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-93»

theorem affine_change_of_variables_gradient_hessian
    {n : Type*} [Fintype n] [DecidableEq n]
    (f : EuclideanSpace ℝ n → ℝ) (S : Matrix n n ℝ)
    (s z : EuclideanSpace ℝ n)
    (hf : ContDiff ℝ 2 f) :
    let x := Matrix.toEuclideanLin S z + s
    gradient (fun z' : EuclideanSpace ℝ n => f (Matrix.toEuclideanLin S z' + s)) z =
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)).adjoint (gradient f x) ∧
    fderiv ℝ
        (gradient (fun z' : EuclideanSpace ℝ n => f (Matrix.toEuclideanLin S z' + s))) z =
      ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)).adjoint).comp
        ((fderiv ℝ (gradient f) x).comp
          (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S))) := by
  sorry

end «CAM-Bench-93»
