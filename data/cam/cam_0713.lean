import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-713»

theorem spectralNorm_eq_topSingularValue
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    ‖A‖ = sSup {r : ℝ | ∃ x : EuclideanSpace ℝ n, ‖x‖ = 1 ∧ r = ‖(Matrix.toEuclideanLin A) x‖} := by
  sorry

end «CAM-Bench-713»
