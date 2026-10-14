import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-37»

def GaussianEliminationWithCompletePivoting
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ p : Equiv.Perm (Fin m), ∃ q : Equiv.Perm (Fin n),
    ∃ L : Matrix (Fin m) (Fin m) ℝ, ∃ U : Matrix (Fin m) (Fin n) ℝ,
      Matrix.reindex p q A = L * U ∧
      (∀ i j : Fin m, i < j → L i j = 0) ∧
      (∀ i : Fin m, L i i = 1) ∧
      (∀ i : Fin m, ∀ j : Fin n, j.1 < i.1 → U i j = 0)

theorem reduced_system_same_solution_set
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (mbar : ℕ)
    (hmn : n < m)
    (hmbar : mbar ≤ n)
    (h_rank : A.rank = mbar)
    (p : Equiv.Perm (Fin m))
    (q : Equiv.Perm (Fin n))
    (L : Matrix (Fin m) (Fin m) ℝ)
    (U : Matrix (Fin m) (Fin n) ℝ)
    (hgecp : Matrix.reindex p q A = L * U)
    (hL_lower : ∀ i j : Fin m, i < j → L i j = 0)
    (hL_diag : ∀ i : Fin m, L i i = 1)
    (hU_upper : ∀ i : Fin m, ∀ j : Fin n, j.1 < i.1 → U i j = 0)
    (hzero : ∀ i : Fin m, mbar ≤ i.1 → ∀ j : Fin n, U i j = 0) :
    ∀ x : Fin n → ℝ,
      let PA : Matrix (Fin m) (Fin n) ℝ := Matrix.reindex p (Equiv.refl (Fin n)) A
      let Pb : Fin m → ℝ := fun i => b (p.symm i)
      let hmbarm : mbar ≤ m := le_trans hmbar (Nat.le_of_lt hmn)
      Matrix.mulVec A x = b ↔
        Matrix.mulVec (PA.submatrix (Fin.castLE hmbarm) id) x =
          fun i : Fin mbar => Pb (Fin.castLE hmbarm i) := by
  sorry

end «CAM-Bench-37»
