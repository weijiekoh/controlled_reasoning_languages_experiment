import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-481»

def IsPolyhedron {n m k : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ A : Matrix (Fin m) (Fin n) ℝ,
    ∃ F : Matrix (Fin k) (Fin n) ℝ,
      ∃ b : Fin m → ℝ,
        ∃ g : Fin k → ℝ,
          P = {x | A.mulVec x ≤ b ∧ F.mulVec x = g}

theorem S_eq_nonneg_and_le_one_and_isPolyhedron (n : ℕ) :
    let S : Set (Fin n → ℝ) :=
      {x | 0 ≤ x ∧ ∀ y : Fin n → ℝ, (∑ i, |y i|) = 1 → ∑ i, x i * y i ≤ 1}
    S = {x | 0 ≤ x ∧ x ≤ fun _ => 1} ∧
      ∃ m k : ℕ, @IsPolyhedron n m k S := by
  sorry

end «CAM-Bench-481»
