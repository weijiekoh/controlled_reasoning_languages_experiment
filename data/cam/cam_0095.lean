import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-95»

def QLinearlyConvergent (x : ℕ → ℝ) (xStar : ℝ) : Prop :=
  ∃ q : ℝ, ∃ N : ℕ,
    0 < q ∧ q < 1 ∧
    ∀ k : ℕ, N ≤ k → |x (k + 1) - xStar| ≤ q * |x k - xStar|

theorem one_div_nat_convergesTo_zero_not_QLinearlyConvergent :
    (∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → |(1 : ℝ) / (k + 1) - 0| < ε) ∧
    ¬ QLinearlyConvergent (fun k : ℕ => (1 : ℝ) / (k + 1)) 0 := by
  sorry

end «CAM-Bench-95»
