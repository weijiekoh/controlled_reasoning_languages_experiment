import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-265»

theorem convexOn_sq_div_of_nonneg_of_pos_of_concave
    {n : ℕ} {f g : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ Set.univ f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hg : ConcaveOn ℝ Set.univ g)
    (hg_pos : ∀ x, 0 < g x) :
    ConvexOn ℝ Set.univ (fun x => (f x) ^ 2 / g x) := by
  sorry

end «CAM-Bench-265»
