import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-669»

open scoped BigOperators

theorem covariance_lower_bound_constraint_is_convex
    {n k : ℕ} (α : Fin n → Fin k → ℝ) (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.IsSymm) :
    Convex ℝ
      {p : Fin n → ℝ |
        (∀ i, 0 ≤ p i) ∧
        (∑ i, p i = 1) ∧
        Matrix.PosSemidef
          ((∑ i, p i •
              Matrix.vecMulVec
                (fun a => α i a - ∑ l, p l * α l a)
                (fun b => α i b - ∑ l, p l * α l b)) - S)} := by
  sorry

end «CAM-Bench-669»
