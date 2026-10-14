import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-510»

open scoped BigOperators

theorem log_neg_log_sum_exp_convex_on_domain {n : ℕ} (b : Fin n → ℝ) :
    ConvexOn ℝ
      {x : Fin n → ℝ | ∑ i, Real.exp (x i + b i) < 1}
      (fun x => -Real.log (-Real.log (∑ i, Real.exp (x i + b i)))) := by
  sorry

end «CAM-Bench-510»
