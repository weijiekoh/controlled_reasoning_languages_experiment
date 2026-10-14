import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-458»

theorem pointed_closed_convex_cone_iff_eq_zero_or_ray_or_sector
    (K : Set (Fin 2 → ℝ))
    (h_closed : IsClosed K)
    (h_cone : ∀ ⦃x : Fin 2 → ℝ⦄, x ∈ K → ∀ ⦃t : ℝ⦄, 0 ≤ t → t • x ∈ K)
    (h_convex : Convex ℝ K) :
    (K ∩ {x | -x ∈ K} = ({0} : Set (Fin 2 → ℝ))) ↔
      K = ({0} : Set (Fin 2 → ℝ)) ∨
        (∃ x : Fin 2 → ℝ,
          x ≠ 0 ∧
            K = {y | ∃ t : ℝ, 0 ≤ t ∧ y = t • x}) ∨
        (∃ x y : Fin 2 → ℝ,
          LinearIndependent ℝ ![x, y] ∧
            {z | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = s • x + t • y} ≠ (Set.univ : Set (Fin 2 → ℝ)) ∧
            K = {z | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = s • x + t • y}) := by
  sorry

end «CAM-Bench-458»
