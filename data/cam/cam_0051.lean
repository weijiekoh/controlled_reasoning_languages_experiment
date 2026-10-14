import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-51»

def IsMinimumNormSolution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) (xStar : n → ℝ) : Prop :=
  A.mulVec xStar = b ∧ ∀ x : n → ℝ, A.mulVec x = b → ‖xStar‖ ≤ ‖x‖

theorem particular_solution_eq_transpose_mul_inv_gram
    {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin (n - m)) ℝ)
    (b : Fin m → ℝ)
    (hfull : Function.Surjective A.mulVec)
    (hrank : A.rank = m)
    (hB_inv : Invertible B)
    [Invertible (A * A.transpose)]
    (hA_decomp :
      let idxN : Fin (n - m) → Fin n :=
        (Fin.cast (Nat.add_sub_of_le hmn)) ∘ Fin.natAdd m
      A.submatrix id (Fin.castLE hmn) = B ∧
        A.submatrix id idxN = N) :
    let Y : Matrix (Fin n) (Fin m) ℝ :=
      fun i j =>
        if h : i.1 < m then
          if j = ⟨i.1, h⟩ then 1 else 0
        else
          (((⅟ B) * N).transpose) ⟨i.1 - m, by omega⟩ j
    let AY : Matrix (Fin m) (Fin m) ℝ := A * Y
    let AAT : Matrix (Fin m) (Fin m) ℝ := A * A.transpose
    Y * Ring.inverse AY = A.transpose * Ring.inverse AAT := by
  sorry

end «CAM-Bench-51»
