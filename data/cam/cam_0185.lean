import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-185»

theorem gordan_theorem
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (R : Matrix (Fin m) (Fin n) ℝ) :
    (∃ x : Fin n → ℝ, ∀ i : Fin m, 0 < (R.mulVec x) i) ↔
      ¬ ∃ p : Fin m → ℝ,
        Rᵀ.mulVec p = 0 ∧
        (∀ i : Fin m, 0 ≤ p i) ∧
        p ≠ 0 := by
  sorry

end «CAM-Bench-185»
