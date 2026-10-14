import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-715»

open Matrix
open scoped MatrixOrder

def IsSpectralNuclearDualPair
    {K : Type*} {m : Type*} {n : Type*} [RCLike K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (spectralNorm nuclearNorm : Matrix m n K → ℝ) : Prop :=
  ∀ B : Matrix m n K,
    nuclearNorm B =
      sSup
        {r : ℝ |
          ∃ A : Matrix m n K,
            spectralNorm A ≤ 1 ∧ r = ‖Matrix.trace (A.conjTranspose * B)‖}

theorem abs_matrix_inner_le_spectral_mul_nuclear
    {K : Type*} {m : Type*} {n : Type*} [RCLike K] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (spectralNorm nuclearNorm : Matrix m n K → ℝ)
    (hdual : IsSpectralNuclearDualPair spectralNorm nuclearNorm)
    (hspec_nonneg : ∀ A : Matrix m n K, 0 ≤ spectralNorm A)
    (A B : Matrix m n K) :
    ‖Matrix.trace (A.conjTranspose * B)‖ ≤ spectralNorm A * nuclearNorm B := by
  sorry

end «CAM-Bench-715»
