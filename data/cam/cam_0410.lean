import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-410»

def SelfConcordantOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧
  ConvexOn ℝ s f ∧
  IsOpen s ∧
  ContDiffOn ℝ 3 f s ∧
  ∀ x ∈ s, ∀ h : E,
    (∀ τ : ℝ, τ ∈ Set.Icc (-1 : ℝ) 1 → x + τ • h ∈ s) →
      |(fderiv ℝ (fun y => (fderiv ℝ (fun z => (fderiv ℝ f z) h) y) h) x) h| ≤
        2 * Real.rpow ((fderiv ℝ (fun y => (fderiv ℝ f y) h) x) h) (3 / 2 : ℝ)

theorem xlogx_not_selfConcordantOn_pos :
    ¬ SelfConcordantOn {x : ℝ | 0 < x} (fun x => x * Real.log x) := by
  sorry

end «CAM-Bench-410»
