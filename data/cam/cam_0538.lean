import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-538»

def IsSymmetricSet (C : Set (Fin n → ℝ)) : Prop :=
  ∀ ⦃x : Fin n → ℝ⦄, x ∈ C → -x ∈ C

def IsExtendedVectorNorm {n : ℕ} (M : (Fin n → ℝ) → ENNReal) : Prop :=
  M 0 = 0 ∧
    (∀ x : Fin n → ℝ, M x = 0 → x = 0) ∧
      (∀ (a : ℝ) (x : Fin n → ℝ), M (a • x) = ENNReal.ofReal |a| * M x) ∧
        ∀ x y : Fin n → ℝ, M (x + y) ≤ M x + M y

theorem minkowskiFunctional_isNorm_with_unitBall
    {n : ℕ}
    (C : Set (Fin n → ℝ))
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hC_symm : IsSymmetricSet C)
    (hC_zero_mem_interior : (0 : Fin n → ℝ) ∈ interior C) :
    let M_C : (Fin n → ℝ) → ENNReal :=
      fun x => sInf {t : ENNReal | 0 < t ∧ ((t.toReal)⁻¹ • x) ∈ C}
    IsExtendedVectorNorm M_C ∧
      ({x : Fin n → ℝ | M_C x ≤ 1} : Set (Fin n → ℝ)) = C := by
  sorry

end «CAM-Bench-538»
