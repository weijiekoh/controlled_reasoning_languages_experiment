import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-490»

theorem gradient_eq_zero_of_saddle_point
    {n m : ℕ}
    {f : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → ℝ}
    {xz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)}
    (hf : DifferentiableAt ℝ f xz)
    (hleft :
      ∀ z : EuclideanSpace ℝ (Fin m),
        f (xz.1, z) ≤ f xz)
    (hright :
      ∀ x : EuclideanSpace ℝ (Fin n),
        f xz ≤ f (x, xz.2)) :
    fderiv ℝ f xz = 0 := by
  sorry

end «CAM-Bench-490»
