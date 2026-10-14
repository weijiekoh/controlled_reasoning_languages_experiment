import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-227»

theorem continuedFraction4_convexOn_and_decreasing :
    let f : (Fin 4 → ℝ) → ℝ :=
      fun x => 1 / (x 0 - 1 / (x 1 - 1 / (x 2 - 1 / x 3)))
    let D : Set (Fin 4 → ℝ) :=
      {x | 0 < x 3 ∧
        0 < x 2 - 1 / x 3 ∧
        0 < x 1 - 1 / (x 2 - 1 / x 3) ∧
        0 < x 0 - 1 / (x 1 - 1 / (x 2 - 1 / x 3))}
    ConvexOn ℝ D f ∧
      ∀ ⦃x y : Fin 4 → ℝ⦄,
        x ∈ D →
        y ∈ D →
        (∀ i : Fin 4, x i ≤ y i) →
        f y ≤ f x := by
  sorry

end «CAM-Bench-227»
