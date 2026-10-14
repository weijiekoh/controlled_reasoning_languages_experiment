import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-515»

theorem quadratic_over_affine_isConvexOn
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :
    ConvexOn ℝ
      {x : Fin n → ℝ | dotProduct c x + d > 0}
      (fun x => dotProduct (A.mulVec x + b) (A.mulVec x + b) / (dotProduct c x + d)) := by
  sorry

end «CAM-Bench-515»
