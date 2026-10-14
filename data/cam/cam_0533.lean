import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-533»

theorem mul_convexOn_of_monotone
    {I : Set ℝ} (hI : Convex ℝ I)
    {f g : ℝ → ℝ}
    (hf_pos : ∀ ⦃x⦄, x ∈ I → 0 < f x)
    (hg_pos : ∀ ⦃x⦄, x ∈ I → 0 < g x)
    (hf_convex : ConvexOn ℝ I f)
    (hg_convex : ConvexOn ℝ I g)
    (hmono :
      (MonotoneOn f I ∧ MonotoneOn g I) ∨
      (AntitoneOn f I ∧ AntitoneOn g I)) :
    ConvexOn ℝ I (fun x => f x * g x) := by
  sorry

end «CAM-Bench-533»
