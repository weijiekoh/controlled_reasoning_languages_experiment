import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-191»

theorem hFromPositiveIncreasingConvex_convexOn_nonneg
    (f : ℝ → ℝ)
    (hf_pos : ∀ s, 0 ≤ s → 0 < f s)
    (hf_mono : Monotone f)
    (hf_convex : ConvexOn ℝ {s : ℝ | 0 ≤ s} f) :
    ConvexOn ℝ {d : ℝ | 0 ≤ d}
      (fun d =>
        if d = 0 then 0
        else sInf ((fun s : ℝ => (d / s) * f s) '' {s : ℝ | s > 0})) := by
  sorry

end «CAM-Bench-191»
