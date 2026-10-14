import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-67»

def KKTMatrix {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (G : Matrix n n ℝ) (A : Matrix m n ℝ) : Matrix (Sum n m) (Sum n m) ℝ :=
  Matrix.fromBlocks G Aᵀ A 0

theorem KKTMatrix_inv_eq_fromBlocks
    {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (G : Matrix n n ℝ) (A : Matrix m n ℝ)
    [Invertible G] [Invertible (A * ⅟ G * Aᵀ)] :
    KKTMatrix G A *
        Matrix.fromBlocks
          (⅟ G - ⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ) * A * ⅟ G)
          (⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))
          ((⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))ᵀ)
          (-⅟ (A * ⅟ G * Aᵀ)) = 1 ∧
      Matrix.fromBlocks
          (⅟ G - ⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ) * A * ⅟ G)
          (⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))
          ((⅟ G * Aᵀ * ⅟ (A * ⅟ G * Aᵀ))ᵀ)
          (-⅟ (A * ⅟ G * Aᵀ)) *
        KKTMatrix G A = 1 := by
  sorry

end «CAM-Bench-67»
