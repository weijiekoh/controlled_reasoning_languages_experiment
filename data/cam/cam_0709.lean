import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-709»

open Matrix

structure VectorNorm (n : ℕ) where
  norm : (Fin n → ℝ) → ℝ
  nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x
  eq_zero_iff : ∀ x : Fin n → ℝ, norm x = 0 ↔ x = 0
  smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x
  add_le : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y

def IsInducedOperatorNormValue {n : ℕ}
    (N : VectorNorm n) (A : Matrix (Fin n) (Fin n) ℝ) (value : ℝ) : Prop :=
  (∀ x : Fin n → ℝ, x ≠ 0 → N.norm (A.mulVec x) / N.norm x ≤ value) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ x : Fin n → ℝ, x ≠ 0 ∧ value < N.norm (A.mulVec x) / N.norm x + ε

theorem frobenius_norm_not_induced_by_vector_norm :
    ∀ n : ℕ, 2 ≤ n →
    ¬ ∃ (N : VectorNorm n),
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        IsInducedOperatorNormValue N A
          (Real.sqrt (∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2)) := by
  sorry

end «CAM-Bench-709»
