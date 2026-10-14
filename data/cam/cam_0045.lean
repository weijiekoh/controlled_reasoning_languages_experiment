import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-45»

open scoped Matrix

def centralityResidualNorm (x s : Fin 2 → ℝ) : ℝ :=
  let μ : ℝ := ((x 0) * (s 0) + (x 1) * (s 1)) / 2
  Real.sqrt ((x 0 * s 0 - μ) ^ 2 + (x 1 * s 1 - μ) ^ 2)

theorem exists_pos_pair_violating_theta_neighborhood :
    ∃ x s : Fin 2 → ℝ,
      (∀ i, 0 < x i) ∧
      (∀ i, 0 < s i) ∧
      ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
        θ * ((x 0) * (s 0) + (x 1) * (s 1)) / 2 <
          centralityResidualNorm x s := by
  sorry

end «CAM-Bench-45»
