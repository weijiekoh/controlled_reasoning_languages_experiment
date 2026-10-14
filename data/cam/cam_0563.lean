import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-563»

theorem integral_average_convex_on_Ioi
    {f F : ℝ → ℝ}
    (hfdiff : Differentiable ℝ f)
    (hf : ConvexOn ℝ Set.univ f)
    (hF : ∀ x > 0, F x = x⁻¹ * ∫ t in 0..x, f t)
    : ConvexOn ℝ (Set.Ioi (0 : ℝ)) F := by
  sorry

end «CAM-Bench-563»
