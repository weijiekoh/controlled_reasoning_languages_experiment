import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-505»

def euclideanNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

theorem norm_affine_map_convex
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (b : m → ℝ) (x y : n → ℝ) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    euclideanNorm (A.mulVec (θ • x + (1 - θ) • y) - b) ≤
      θ * euclideanNorm (A.mulVec x - b) + (1 - θ) * euclideanNorm (A.mulVec y - b) := by
  sorry

end «CAM-Bench-505»
