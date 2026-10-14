import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-660»

structure SmoothedAbsoluteResidualProblem where
  n : ℕ
  m : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  ε : ℝ
  ε_pos : 0 < ε

def SmoothedAbsoluteResidualProblem.objective
    (p : SmoothedAbsoluteResidualProblem) (x : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m, Real.sqrt (((∑ j : Fin p.n, p.A i j * x j) - p.b i) ^ 2 + p.ε)

def SmoothedAbsoluteResidualProblem.isMinimizer
    (p : SmoothedAbsoluteResidualProblem) (x : Fin p.n → ℝ) : Prop :=
  ∀ y : Fin p.n → ℝ, p.objective x ≤ p.objective y

theorem least_absolute_deviations_opt_value_ge_smoothed_residual_bound
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hrank : LinearMap.ker (Matrix.toLin' A) = ⊥)
    (ε : ℝ)
    (εpos : 0 < ε)
    (xhat : Fin n → ℝ)
    (hxhat :
      ∀ y : Fin n → ℝ,
        (SmoothedAbsoluteResidualProblem.objective
          { n := n, m := m, A := A, b := b, ε := ε, ε_pos := εpos } xhat) ≤
          (SmoothedAbsoluteResidualProblem.objective
            { n := n, m := m, A := A, b := b, ε := ε, ε_pos := εpos } y)) :
    sInf {v : ℝ |
        ∃ x : Fin n → ℝ,
          v = ∑ i : Fin m, |(∑ j : Fin n, A i j * x j) - b i|} ≥
      ∑ i : Fin m,
        (((∑ j : Fin n, A i j * xhat j) - b i) ^ 2) /
          Real.sqrt ((((∑ j : Fin n, A i j * xhat j) - b i) ^ 2) + ε) := by
  sorry

end «CAM-Bench-660»
