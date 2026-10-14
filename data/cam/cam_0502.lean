import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-502»

theorem f_convex_on_D_trigonometric_log_integral
    (n : ℕ) :
    ConvexOn ℝ
      {x : Fin (n + 1) → ℝ | ∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 * Real.pi →
        0 <
          x 0 + ∑ i : Fin n, x i.succ * Real.cos (((i : ℕ) : ℝ) * ω)}
      (fun x =>
        -∫ ω in (0 : ℝ)..(2 * Real.pi),
          Real.log (x 0 + ∑ i : Fin n, x i.succ * Real.cos (((i : ℕ) : ℝ) * ω))) := by
  sorry

end «CAM-Bench-502»
