import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-109»

theorem exists_differentiable_function_with_large_value_and_small_interpolation_step
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧
      ∃ α₀ : ℝ, 0 < α₀ ∧
        let α₁ :=
          -((deriv φ 0) * α₀ ^ 2) /
            (2 * (φ α₀ - φ 0 - (deriv φ 0) * α₀))
        φ α₀ ≥ ε⁻¹ ∧ |α₁| ≤ ε := by
  sorry

end «CAM-Bench-109»
