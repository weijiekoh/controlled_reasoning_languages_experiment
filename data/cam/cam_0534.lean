import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-534»

theorem concaveOn_mul_of_opposite_monotone
    {f g : ℝ → ℝ}
    (hf_pos : ∀ x : ℝ, 0 < f x)
    (hg_pos : ∀ x : ℝ, 0 < g x)
    (hf_concave : ConcaveOn ℝ Set.univ f)
    (hg_concave : ConcaveOn ℝ Set.univ g)
    (hmono :
      (Monotone f ∧ Antitone g) ∨
      (Antitone f ∧ Monotone g)) :
    ConcaveOn ℝ Set.univ (fun x => f x * g x) := by
  sorry

end «CAM-Bench-534»
