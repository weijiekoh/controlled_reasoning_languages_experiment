import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-261»

theorem convexOn_norm_comp_of_convex_nondecreasing
    {n : ℕ} (h : ℝ → ℝ)
    (h_convex : ConvexOn ℝ Set.univ h)
    (h_mono : Monotone h)
    (h_nonpos : ∀ t ≤ 0, h t = h 0) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => h ‖x‖) := by
  sorry

end «CAM-Bench-261»
