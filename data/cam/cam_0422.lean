import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-422»

open scoped BigOperators

theorem quadratic_sublevelSet_convex
    {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b : n → ℝ) (c : ℝ)
    (hA : A.IsSymm) (hpsd : Matrix.PosSemidef A) :
    Convex ℝ {x : n → ℝ | dotProduct x (A.mulVec x) + (∑ i, b i * x i) + c ≤ 0} := by
  sorry

end «CAM-Bench-422»
