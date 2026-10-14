import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-7»

open scoped Matrix

theorem norm_rankOne_projection_eq_one
    (n : ℕ) (s : EuclideanSpace ℝ (Fin n))
    (hs : s ≠ 0) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        ((((‖s‖ ^ 2 : ℝ)⁻¹) • Matrix.vecMulVec s s : Matrix (Fin n) (Fin n) ℝ))‖ = (1 : ℝ) := by
  sorry

end «CAM-Bench-7»
