import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-742»

def secondOrderCone (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  {p | ‖p.1‖ ≤ p.2}

open scoped RealInnerProductSpace

theorem secondOrderCone_isSelfDual (n : ℕ) :
    {q : EuclideanSpace ℝ (Fin n) × ℝ |
      ∀ p ∈ secondOrderCone n, 0 ≤ ⟪p.1, q.1⟫ + p.2 * q.2} = secondOrderCone n := by
  sorry

end «CAM-Bench-742»
