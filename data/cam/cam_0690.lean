import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-690»

theorem nearestPointProperty_nonempty_and_isClosed
    {n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC :
      ∀ x0 : EuclideanSpace ℝ (Fin n),
        ∃! c : EuclideanSpace ℝ (Fin n),
          c ∈ C ∧ ∀ y : EuclideanSpace ℝ (Fin n), y ∈ C → ‖x0 - c‖ ≤ ‖x0 - y‖) :
    C.Nonempty ∧ IsClosed C := by
  sorry

end «CAM-Bench-690»
