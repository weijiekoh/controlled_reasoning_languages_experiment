import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-165»

def polar (C : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ C, dotProduct y x ≤ 1}

theorem polar_simplex_eq_iInter
    (n : ℕ) (hn : 0 < n) :
    polar
      {x : Fin n → ℝ | (∑ i, x i) = 1 ∧ ∀ i, 0 ≤ x i} =
      {y : Fin n → ℝ | ∀ i, y i ≤ 1} := by
  sorry

end «CAM-Bench-165»
