import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-532»

theorem inf_rescaling_convex
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : V → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    let g : V → WithBot ℝ :=
      fun x => sInf {r : WithBot ℝ | ∃ α : ℝ, 0 < α ∧ r = ((f (α • x) / α : ℝ) : WithBot ℝ)}
    ∀ x y : V, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (t • x + (1 - t) • y) ≤
        ((t : ℝ) : WithBot ℝ) * g x + ((1 - t : ℝ) : WithBot ℝ) * g y := by
  sorry

end «CAM-Bench-532»
