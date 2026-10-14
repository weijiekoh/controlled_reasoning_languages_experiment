import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-503»

theorem convex_le_secant_on_interval
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {a b x : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b) :
    f x ≤ ((b - x) / (b - a)) * f a + ((x - a) / (b - a)) * f b := by
  sorry

end «CAM-Bench-503»
