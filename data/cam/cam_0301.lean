import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-301»

theorem exists_not_convex_Sm :
    ∃ m : ℕ,
      ¬ Convex ℝ
        {p : Fin m → ℝ |
          (∀ j, 0 ≤ p j) ∧
            (Finset.card (Finset.univ.filter fun j : Fin m => 0 < p j) ≤ m / 2)} := by
  sorry

end «CAM-Bench-301»
