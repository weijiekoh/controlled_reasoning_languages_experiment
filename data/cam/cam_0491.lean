import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-491»

theorem log_eq_tendsto_uAlpha_at_zero
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun α : ℝ => (x ^ α - 1) / α)
      (𝓝[fun α : ℝ => 0 < α ∧ α ≤ 1] (0 : ℝ)) (𝓝 (Real.log x)) := by
  sorry

end «CAM-Bench-491»
