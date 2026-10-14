import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-190»

theorem perspective_convex_on_nonneg_pos
    {f : ℝ → ℝ}
    (hf_pos : ∀ v : ℝ, 0 ≤ v → 0 < f v)
    (hf_mono : MonotoneOn f (Set.Ici (0 : ℝ)))
    (hf_convex : ConvexOn ℝ (Set.Ici (0 : ℝ)) f) :
    ConvexOn ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 < p.2} (fun p : ℝ × ℝ => p.2 * f (p.1 / p.2)) := by
  sorry

end «CAM-Bench-190»
