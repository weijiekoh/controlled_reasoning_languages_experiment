import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-430»

theorem convex_translate_subset_set
    {n : Type*} [AddCommGroup n] [Module ℝ n]
    (S₁ S₂ : Set n) (hS₁ : Convex ℝ S₁) :
    Convex ℝ {x : n | ∀ s ∈ S₂, x + s ∈ S₁} := by
  sorry

end «CAM-Bench-430»
