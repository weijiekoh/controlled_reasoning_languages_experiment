import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-661»

structure PairedResidualMinimizationProblem where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  φ : ℝ → ℝ

def PairedResidualMinimizationProblem.residual
    (p : PairedResidualMinimizationProblem) (x : Fin p.n → ℝ) : Fin p.m → ℝ :=
  fun i => (∑ j : Fin p.n, p.A i j * x j) - p.b i

def PairedResidualMinimizationProblem.l1ObjectiveFn
    (p : PairedResidualMinimizationProblem) (x : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m, |p.residual x i|

def PairedResidualMinimizationProblem.separableObjectiveFn
    (p : PairedResidualMinimizationProblem) (x : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.m, p.φ (p.residual x i)

abbrev PairedResidualMinimizationProblem.l1Objective :=
  PairedResidualMinimizationProblem.l1ObjectiveFn

abbrev PairedResidualMinimizationProblem.separableObjective :=
  PairedResidualMinimizationProblem.separableObjectiveFn

theorem l1_objective_of_separable_optimal_le
    (p : PairedResidualMinimizationProblem)
    (ε : ℝ)
    (hε : 0 < ε)
    (hRank : LinearIndependent ℝ (fun j : Fin p.n => fun i : Fin p.m => p.A i j))
    (hφ : p.φ = fun u : ℝ => Real.sqrt (u ^ 2 + ε))
    (xhat : Fin p.n → ℝ)
    (hxhat_opt : ∀ x : Fin p.n → ℝ, p.separableObjective xhat ≤ p.separableObjective x)
    (pstar : ℝ)
    (xstar : Fin p.n → ℝ)
    (hxstar_opt : ∀ x : Fin p.n → ℝ, p.l1Objective xstar ≤ p.l1Objective x)
    (hpstar : pstar = p.l1Objective xstar) :
    p.l1Objective xhat ≤
      pstar +
        ∑ i : Fin p.m,
          |p.residual xhat i| *
            (1 -
              |p.residual xhat i| /
                Real.sqrt ((p.residual xhat i) ^ 2 + ε)) := by
  sorry

end «CAM-Bench-661»
