import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-721»

theorem gradient_eq_zero_of_saddle
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    {xbar : EuclideanSpace ℝ (Fin n)}
    {zbar : EuclideanSpace ℝ (Fin m)}
    (hf : Differentiable ℝ f)
    (hsaddle :
      ∀ x z,
        f (xbar, z) ≤ f (xbar, zbar) ∧
        f (xbar, zbar) ≤ f (x, zbar)) :
    fderiv ℝ f (xbar, zbar) = 0 := by
  sorry

end «CAM-Bench-721»
