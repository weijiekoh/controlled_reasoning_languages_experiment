import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-3»

theorem squared_norm_residual_convex
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (J : E →ₗ[ℝ] F) (y : F) :
    ConvexOn ℝ Set.univ (fun x : E => (1 / 2 : ℝ) * ‖J x - y‖ ^ 2) := by
  sorry

end «CAM-Bench-3»
