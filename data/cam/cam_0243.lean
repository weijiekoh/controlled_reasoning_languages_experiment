import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-243»

open scoped RealInnerProductSpace

theorem convexOn_neg_exp_neg_of_hessian_gradient_block_pos
    {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hess : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : Convex ℝ D)
    (hg : ContDiffOn ℝ 2 g D)
    (hgrad : ∀ x ∈ D, HasGradientAt g (G x) x)
    (hhess : ∀ x ∈ D, HasFDerivAt G (hess x) x)
    (hblock :
      ∀ x ∈ D, ∀ (u : EuclideanSpace ℝ (Fin n)) (s : ℝ),
        0 ≤ ⟪hess x u, u⟫ + 2 * s * ⟪G x, u⟫ + s ^ 2) :
    ConvexOn ℝ D (fun x => -Real.exp (-g x)) := by
  sorry

end «CAM-Bench-243»
