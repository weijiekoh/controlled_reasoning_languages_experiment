import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-364»

theorem edMatrices_convex_cone
    {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hXs : X.IsSymm)
    (hX : ∃ m : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin m),
      ∀ i j, X i j = ‖p i - p j‖ ^ 2)
    (hYs : Y.IsSymm)
    (hY : ∃ m : ℕ, ∃ q : Fin n → EuclideanSpace ℝ (Fin m),
      ∀ i j, Y i j = ‖q i - q j‖ ^ 2)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (α • X + β • Y).IsSymm ∧
    ∃ m : ℕ, ∃ r : Fin n → EuclideanSpace ℝ (Fin m),
      ∀ i j, (α • X + β • Y) i j = ‖r i - r j‖ ^ 2 := by
  sorry

end «CAM-Bench-364»
