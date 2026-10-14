import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-202»

def euclideanLength {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

def spectralNormValues {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Set ℝ :=
  {r : ℝ | ∃ x : n → ℝ, euclideanLength x = 1 ∧ euclideanLength (A.mulVec x) = r}

def spectralNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ :=
  sSup (spectralNormValues A)

theorem fS_eq_inf_closedBall_radius
    {m p : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty) (X : Matrix (Fin p) (Fin m) ℝ)
    (hspec_nonempty :
      ∀ y : Fin p → ℝ,
        (spectralNormValues
          (X.submatrix id (fun i : {j // j ∈ S} => (i : Fin m)) -
            Matrix.of fun i _ => y i)).Nonempty)
    (hspec_bddAbove :
      ∀ y : Fin p → ℝ,
        BddAbove
          (spectralNormValues
            (X.submatrix id (fun i : {j // j ∈ S} => (i : Fin m)) -
              Matrix.of fun i _ => y i)))
    (hleft_bddBelow :
      BddBelow
        (Set.range fun y : Fin p → ℝ =>
          spectralNorm (X.submatrix id (fun i : {j // j ∈ S} => (i : Fin m)) -
            Matrix.of fun i _ => y i)))
    (hright_bddBelow :
      BddBelow
        {r : ℝ | 0 ≤ r ∧ ∃ y : Fin p → ℝ,
          ∀ j : {k // k ∈ S}, euclideanLength ((fun i : Fin p => X i (j : Fin m)) - y) ≤ r}) :
    sInf (Set.range fun y : Fin p → ℝ =>
      spectralNorm (X.submatrix id (fun i : {j // j ∈ S} => (i : Fin m)) -
        Matrix.of fun i _ => y i)) =
    sInf {r : ℝ | 0 ≤ r ∧ ∃ y : Fin p → ℝ,
      ∀ j : {k // k ∈ S}, euclideanLength ((fun i : Fin p => X i (j : Fin m)) - y) ≤ r} := by
  sorry

end «CAM-Bench-202»
