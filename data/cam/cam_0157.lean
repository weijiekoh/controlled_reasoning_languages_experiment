import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-157»

def exponentialCone : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.2.1 ∧ p.2.1 * Real.exp (p.1 / p.2.1) ≤ p.2.2}

def dualCone {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {u | ∀ x ∈ K, 0 ≤ ∑ i, u i * x i}

theorem dualCone_exponentialCone_eq :
    dualCone
        {u : Fin 3 → ℝ |
          ∃ p ∈ exponentialCone,
            u 0 = p.1 ∧ u 1 = p.2.1 ∧ u 2 = p.2.2} =
      ({u : Fin 3 → ℝ |
          u 0 < 0 ∧ u 2 ≥ -(u 0) * Real.exp (u 1 / u 0 - 1)} ∪
        {u : Fin 3 → ℝ | u 0 = 0 ∧ 0 ≤ u 1 ∧ 0 ≤ u 2}) := by
  sorry

end «CAM-Bench-157»
