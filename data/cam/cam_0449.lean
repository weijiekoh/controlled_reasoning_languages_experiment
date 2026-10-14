import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-449»

theorem exists_strictly_positive_solution_iff_no_dual_certificate
    {m n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A.mulVec x = b) ↔
      ¬ ∃ lam : Fin m → ℝ,
        (∀ i, 0 ≤ (A.transpose.mulVec lam) i) ∧
        (A.transpose.mulVec lam ≠ 0 ∨ dotProduct b lam < 0) ∧
        dotProduct b lam ≤ 0 := by
  sorry

end «CAM-Bench-449»
