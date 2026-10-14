import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-257»

theorem weightedGeomMonomial_convexOn_of_nonpos
    {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, θ i ≤ 0) :
    ConvexOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => ∏ i, (x i) ^ (θ i)) := by
  sorry

end «CAM-Bench-257»
