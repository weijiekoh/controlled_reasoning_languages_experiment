import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-550»

theorem convex_iff_integral_midpoint_bound
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) (hf_cont : Continuous f) :
    ConvexOn ℝ (Set.univ : Set ((Fin n → ℝ))) f ↔
      ∀ x y : Fin n → ℝ,
        ∫ t in (0 : ℝ)..1, f (x + t • (y - x)) ≤ (f x + f y) / 2 := by
  sorry

end «CAM-Bench-550»
