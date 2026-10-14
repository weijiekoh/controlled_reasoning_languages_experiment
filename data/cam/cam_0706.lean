import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-706»

open scoped BigOperators

theorem steepest_descent_direction_solves_quadratic_model
    {n : ℕ} (N : Seminorm ℝ (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x)
    (Δx_nsd Δx_sd : Fin n → ℝ)
    (hnorm_nonneg : ∀ v : Fin n → ℝ, 0 ≤ N v)
    (hΔx_nsd :
      N Δx_nsd ≤ 1 ∧
      ∀ y : Fin n → ℝ, N y ≤ 1 →
        (fderiv ℝ f x) Δx_nsd ≤ (fderiv ℝ f x) y)
    (hΔx_sd : Δx_sd = |(fderiv ℝ f x) Δx_nsd| • Δx_nsd)
    (hbound : N Δx_nsd = 1) :
    let model : (Fin n → ℝ) → ℝ :=
      fun v => (fderiv ℝ f x) v + (1 / 2 : ℝ) * (N v) ^ 2
    Δx_sd ∈ {v : Fin n → ℝ | ∀ y : Fin n → ℝ, model v ≤ model y} := by
  sorry

end «CAM-Bench-706»
