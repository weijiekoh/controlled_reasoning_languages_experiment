import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-432»

def coneGeneratedByRankFactorizations (n k : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  ⋂₀ {C : Set (Matrix (Fin n) (Fin n) ℝ) |
      {A : Matrix (Fin n) (Fin n) ℝ |
          ∃ X : Matrix (Fin n) (Fin k) ℝ, Matrix.rank X = k ∧ A = X * X.transpose} ⊆ C ∧
        (0 : Matrix (Fin n) (Fin n) ℝ) ∈ C ∧
        (∀ A B : Matrix (Fin n) (Fin n) ℝ, A ∈ C → B ∈ C → A + B ∈ C) ∧
        (∀ A : Matrix (Fin n) (Fin n) ℝ, ∀ t : ℝ, 0 ≤ t → A ∈ C → t • A ∈ C)}

theorem cone_eq_posSemidef_rank_ge_k_union_zero
    (n k : ℕ) (hk₁ : 1 ≤ k) (hk₂ : k ≤ n) :
    coneGeneratedByRankFactorizations n k =
      ({A : Matrix (Fin n) (Fin n) ℝ |
          A.PosSemidef ∧ k ≤ Matrix.rank A} ∪ {0}) := by
  sorry

end «CAM-Bench-432»
