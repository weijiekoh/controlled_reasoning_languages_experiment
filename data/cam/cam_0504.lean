import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-504»

theorem secant_slope_mono_of_convex
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {a b x : ℝ}
    (hab : a < b) (hax : a < x) (hxb : x < b) :
    (f x - f a) / (x - a) ≤ (f b - f a) / (b - a) ∧
      (f b - f a) / (b - a) ≤ (f b - f x) / (b - x) := by
  sorry

end «CAM-Bench-504»
