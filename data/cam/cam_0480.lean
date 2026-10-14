import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-480»

open scoped RealInnerProductSpace

def halfspace {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (d : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ⟪c, x⟫ ≤ d}

theorem norm_sub_le_norm_sub_is_halfspace_explicit {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)) (hab : a ≠ b) :
    ∃ (c : EuclideanSpace ℝ (Fin n)) (d : ℝ),
      {x : EuclideanSpace ℝ (Fin n) | ‖x - a‖ ≤ ‖x - b‖} = halfspace c d ∧
        c = b - a ∧ d = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2 := by
  sorry

end «CAM-Bench-480»
