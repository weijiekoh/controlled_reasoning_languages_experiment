import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-415»

theorem ray_log_homogeneous_hessian_quadratic_form_eq_neg_theta
    {n : ℕ}
    (K : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : (interior (K : Set (EuclideanSpace ℝ (Fin n)))).Nonempty)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (θ : ℝ)
    (hψ_smooth : ∀ y : EuclideanSpace ℝ (Fin n),
      y ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))) →
      ContDiffAt ℝ 2 ψ y)
    (hψ : ∀ (y : EuclideanSpace ℝ (Fin n)),
      y ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))) →
      ∀ t > 0, ψ (t • y) = ψ y + θ * Real.log t) :
    ∀ (y : EuclideanSpace ℝ (Fin n)),
      y ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))) →
      (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => (fderiv ℝ ψ x) y) y) y = -θ := by
  sorry

end «CAM-Bench-415»
