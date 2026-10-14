import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-200»

structure ConvexVarianceControlProblem where
  n : ℕ
  σ : ℝ
  G : Fin n → Fin n → ℝ
  Y : Fin n → Fin n → ℝ
  U : Fin n → Fin n → ℝ
  t : ℝ

def ConvexVarianceControlProblem.is_feasible (p : ConvexVarianceControlProblem) : Prop :=
  (∀ i : Fin p.n, p.σ ^ 2 * ∑ j : Fin p.n, (p.Y i j) ^ 2 ≤ p.t) ∧
    (∀ i : Fin p.n, p.σ ^ 2 * ∑ j : Fin p.n, (p.U i j) ^ 2 ≤ 1) ∧
    ∀ i j : Fin p.n, p.Y i j - (if i = j then (1 : ℝ) else 0) = ∑ k : Fin p.n, p.G i k * p.U k j

def ConvexVarianceControlProblem.objectiveValue (p : ConvexVarianceControlProblem) : ℝ :=
  p.t

theorem feedback_variance_minimax_equivalent_to_convex_variance_control
    (p : ConvexVarianceControlProblem)
    (hYinv : Function.Bijective p.Y) :
    p.is_feasible →
      ∃ F : Fin p.n → Fin p.n → ℝ,
        (∀ i j : Fin p.n, ∑ k : Fin p.n, F i k * p.Y k j = p.U i j) ∧
        ∀ i j : Fin p.n,
          ∑ k : Fin p.n, p.G i k * p.U k j =
            p.Y i j - if i = j then (1 : ℝ) else 0 := by
  sorry

end «CAM-Bench-200»
