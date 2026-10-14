import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-575»

def MatrixConcaveOn
    {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (s : Set (Matrix n n ℝ))
    (F : Matrix n n ℝ → Matrix m m ℝ) : Prop :=
  Convex ℝ s ∧
    (∀ ⦃X : Matrix n n ℝ⦄, X ∈ s → X.IsSymm) ∧
    (∀ ⦃X : Matrix n n ℝ⦄, X ∈ s → (F X).IsSymm) ∧
    ∀ ⦃X : Matrix n n ℝ⦄, X ∈ s →
      ∀ ⦃Y : Matrix n n ℝ⦄, Y ∈ s →
        ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 →
          t • X + (1 - t) • Y ∈ s ∧
            (∀ x : m → ℝ,
              0 ≤ dotProduct x (((F (t • X + (1 - t) • Y)) - (t • F X + (1 - t) • F Y)).mulVec x))

def LoewnerOrder
    {n : Type*} [Fintype n] [DecidableEq n]
    (M N : Matrix n n ℝ) : Prop :=
  M.IsSymm ∧ N.IsSymm ∧
    ∀ x : n → ℝ, 0 ≤ dotProduct x ((M - N).mulVec x)

theorem schurComplement_matrixConcave
    {n k : ℕ}
    (hkn : k ≤ n) :
    let F : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin (n - k)) (Fin (n - k)) ℝ :=
      fun X =>
        let idx1 : Fin k → Fin n := Fin.castLE hkn
        let idx2 : Fin (n - k) → Fin n :=
          Fin.cast (Nat.add_sub_of_le hkn) ∘ Fin.natAdd k
        X.submatrix idx2 idx2 -
          (X.submatrix idx2 idx1 *
            (X.submatrix idx1 idx1)⁻¹ *
            X.submatrix idx1 idx2)
    MatrixConcaveOn
      {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef}
      F := by
  sorry

end «CAM-Bench-575»
