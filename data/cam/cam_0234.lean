import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-234»

open scoped BigOperators

theorem concaveOn_prod_one_sub_exp_neg_rpow
    {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i) :
    ConcaveOn ℝ
      {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, lam i * Real.exp (-x i) ≤ 1}
      (fun x => ∏ i, Real.rpow (1 - Real.exp (-x i)) (lam i)) := by
  sorry

end «CAM-Bench-234»
