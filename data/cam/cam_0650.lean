import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-650»

open Complex

theorem pick_nevanlinna_representation_iff_psd
    {n : ℕ} {z : Fin n → ℂ}
    (hz : Function.Injective z)
    (hz1 : ∀ k, 1 < ‖z k‖) :
    {y : Fin n → ℂ |
      ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f {w : ℂ | 1 < ‖w‖} ∧
        (∀ w : ℂ, 1 < ‖w‖ → 0 ≤ (f w).re) ∧
        ∀ k, f (z k) = y k} =
    {y : Fin n → ℂ |
      (Matrix.toEuclideanLin
        (((fun k l => (y k + star (y l)) / (1 - z k * star (z l))) :
          Matrix (Fin n) (Fin n) ℂ))).IsPositive} := by
  sorry

end «CAM-Bench-650»
