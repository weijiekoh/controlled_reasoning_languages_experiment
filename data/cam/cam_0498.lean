import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-498»

theorem power_sum_root_concave_on_positive_orthant
    {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp_ne : p ≠ 0) (hp_lt : p < 1) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => Real.rpow (∑ i : Fin n, Real.rpow (x i) p) (1 / p)) := by
  sorry

end «CAM-Bench-498»
