import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-355»

theorem matrix_nonnegCone_image_subset_iff_columns
    {n k p : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    {y | ∃ x : Fin k → ℝ, (∀ i, 0 ≤ x i) ∧ y = A.mulVec x} ⊆
        {y | ∃ x : Fin p → ℝ, (∀ i, 0 ≤ x i) ∧ y = B.mulVec x} ↔
      ∀ j : Fin k, ∃ x : Fin p → ℝ, (∀ i, 0 ≤ x i) ∧
        B.mulVec x = A.mulVec (fun i => if i = j then 1 else 0) := by
  sorry

end «CAM-Bench-355»
