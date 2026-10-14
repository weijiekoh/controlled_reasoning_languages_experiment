import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-271»

theorem ratio_squared_norm_affine_over_one_sub_normSq_convexOn
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) :
    ConvexOn ℝ {x : n → ℝ | ‖x‖ < 1}
      (fun x : n → ℝ => ‖A.mulVec x - b‖ ^ 2 / (1 - ‖x‖ ^ 2)) := by
  sorry

end «CAM-Bench-271»
