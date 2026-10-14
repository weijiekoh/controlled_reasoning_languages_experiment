import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-569»

def LogConcaveOnInterval (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Convex ℝ s ∧
  DifferentiableOn ℝ f s ∧
  DifferentiableOn ℝ (deriv f) s ∧
  (∀ x ∈ s, 0 < f x) ∧
  ConcaveOn ℝ s fun x => Real.log (f x)

theorem sq_half_ge_linearized_neg_sq_half (t x : ℝ) :
    t^2 / 2 ≥ x^2 / 2 + x * (t - x) := by
  sorry

end «CAM-Bench-569»
