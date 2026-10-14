import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-231»

theorem exists_convex_radial_profile_of_orthogonal_invariance
    (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_invariant :
      ∀ Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ x : EuclideanSpace ℝ (Fin n), f (Q x) = f x) :
    ∃ φ : ℝ → ℝ,
      (∀ x : EuclideanSpace ℝ (Fin n), f x = φ ‖x‖) ∧
      Monotone φ ∧
      ConvexOn ℝ Set.univ φ := by
  sorry

end «CAM-Bench-231»
