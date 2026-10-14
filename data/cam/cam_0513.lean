import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-513»

open scoped BigOperators

theorem lp_log_barrier_convexOn
    {n : ℕ} {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ
      {xt : (Fin n → ℝ) × ℝ | (∑ i : Fin n, |xt.1 i| ^ p) ^ (1 / p) < xt.2}
      (fun xt : (Fin n → ℝ) × ℝ =>
        -Real.log (xt.2 ^ p - ((∑ i : Fin n, |xt.1 i| ^ p) ^ (1 / p)) ^ p)) := by
  sorry

end «CAM-Bench-513»
