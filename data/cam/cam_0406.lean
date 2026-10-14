import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-406»

open BigOperators

structure EntropyMinimizationProblem where
  n : ℕ
  p : ℕ
  hpn : p < n
  A : Matrix (Fin p) (Fin n) ℝ
  b : Fin p → ℝ

def EntropyMinimizationProblem.objective (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, x i * Real.log (x i)

def EntropyMinimizationProblem.isFeasible (P : EntropyMinimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.n, 0 < x i) ∧ P.A.mulVec x = P.b

theorem entropy_minimization_problem_has_unique_optimal_solution
    (P : EntropyMinimizationProblem)
    (h_nonempty : ∃ x : Fin P.n → ℝ, P.isFeasible x) :
    ∃! x : Fin P.n → ℝ,
      P.isFeasible x ∧
        ∀ y : Fin P.n → ℝ, P.isFeasible y → P.objective x ≤ P.objective y := by
  sorry

end «CAM-Bench-406»
