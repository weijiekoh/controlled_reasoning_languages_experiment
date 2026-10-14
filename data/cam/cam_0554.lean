import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-554»

open scoped BigOperators

theorem differentiable_quasiconvex_iff_gradient_mono
    {n : ℕ} (s : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hs : Convex ℝ s)
    (hqd : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    QuasiconvexOn ℝ s f ↔
      ∀ x ∈ s, ∀ y ∈ s, f y ≤ f x →
        fderiv ℝ f x (y - x) ≤ 0 := by
  sorry

end «CAM-Bench-554»
