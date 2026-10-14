import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-36»

structure CompletePivotingLU where
  n : ℕ
  A : Matrix (Fin n) (Fin n) ℝ
  M : Fin (n + 1) → Matrix (Fin n) (Fin n) ℝ
  rowPerm : Fin n → (Fin n ≃ Fin n)
  colPerm : Fin n → (Fin n ≃ Fin n)
  pivotRow : Fin n → Fin n
  pivotCol : Fin n → Fin n
  L : Matrix (Fin n) (Fin n) ℝ
  U : Matrix (Fin n) (Fin n) ℝ
  start_matrix : M 0 = A
  pivot_in_remaining_rows : ∀ k : Fin n, k ≤ pivotRow k
  pivot_in_remaining_cols : ∀ k : Fin n, k ≤ pivotCol k
  pivot_moved_to_diagonal :
    ∀ k : Fin n,
      rowPerm k (pivotRow k) = k ∧ colPerm k (pivotCol k) = k
  pivot_chosen_from_remaining_submatrix :
    ∀ k : Fin n,
      k ≤ pivotRow k ∧ k ≤ pivotCol k
  pivot_nonzero_after_permutations :
    ∀ k : Fin n,
      Matrix.reindex (rowPerm k) (colPerm k) (M k.castSucc) k k ≠ 0
  elimination_step :
    ∀ k : Fin n,
      ∃ Pk : Matrix (Fin n) (Fin n) ℝ,
        Pk = Matrix.reindex (rowPerm k) (colPerm k) (M k.castSucc) ∧
        M k.succ k k = Pk k k ∧
        (∀ i : Fin n, k < i → M k.succ i k = 0) ∧
        (∀ i j : Fin n, i < k → M k.succ i j = Pk i j) ∧
        (∀ i j : Fin n, j < k → M k.succ i j = Pk i j)
  lowerTriangular : ∀ i j : Fin n, i < j → L i j = 0
  upperTriangular : ∀ i j : Fin n, j < i → U i j = 0
  final_upper_matrix : M (Fin.last n) = U
  final_factorization_from_elimination :
    ∃ Pr Pc : Fin n ≃ Fin n,
      Matrix.reindex Pr Pc A = L * U

def feasible (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Prop :=
  ∃ x : Fin n → ℝ, A.mulVec x = b

theorem feasible_iff_tail_zero_of_complete_pivoting
    (m n r : ℕ) (hmn : n < m)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (P : Fin m ≃ Fin m) (Q : Fin n ≃ Fin n)
    (L : Matrix (Fin m) (Fin m) ℝ)
    (U₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (U₁₂ : Matrix (Fin r) (Fin (n - r)) ℝ)
    (U : Matrix (Fin m) (Fin n) ℝ)
    (hrank : A.rank = r)
    (hrn : r ≤ n)
    (hLlower : ∀ i j : Fin m, i < j → L i j = 0)
    (hUtri : ∀ i j : Fin r, j < i → U₁₁ i j = 0)
    (hUdet : IsUnit U₁₁.det)
    (hUblock : ∀ i : Fin m, r ≤ i.1 → ∀ j : Fin n, U i j = 0)
    (hLU : Matrix.reindex P Q A = L * U)
    (hLinv : IsUnit L.det) :
    (∃ x : Fin n → ℝ, A.mulVec x = b) ↔
      (∀ k : Fin (m - r),
        ((L⁻¹).mulVec (fun j => b (P.symm j))) ⟨r + k.1, by
          have hk : k.1 < m - r := k.2
          omega⟩ = 0) := by
  sorry

end «CAM-Bench-36»
