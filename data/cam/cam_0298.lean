import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-298»

theorem matrix_two_by_two_psd_iff :
    ∀ {x y : ℝ},
      (x * y ≥ 1 ∧ 0 ≤ x ∧ 0 ≤ y) ↔
        Matrix.PosSemidef (Matrix.of fun i j : Fin 2 =>
          match (i : ℕ), (j : ℕ) with
          | 0, 0 => x
          | 0, 1 => 1
          | 1, 0 => 1
          | 1, 1 => y
          | _, _ => 0) := by
  sorry

end «CAM-Bench-298»
