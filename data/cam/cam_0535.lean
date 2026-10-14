import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-535»

theorem convexOn_div_of_convex_nondecreasing_of_concave_nonincreasing
    {I : Set ℝ} {f g : ℝ → ℝ}
    (hI : Convex ℝ I)
    (hf_pos : ∀ ⦃x⦄, x ∈ I → 0 < f x)
    (hg_pos : ∀ ⦃x⦄, x ∈ I → 0 < g x)
    (hf_convex : ConvexOn ℝ I f)
    (hf_mono : MonotoneOn f I)
    (hg_concave : ConcaveOn ℝ I g)
    (hg_antitone : AntitoneOn g I) :
    ConvexOn ℝ I (fun x => f x / g x) := by
  sorry

end «CAM-Bench-535»
