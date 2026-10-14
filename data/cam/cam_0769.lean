import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-769»

def IsLowerBoundEstimate (pStar M : ℝ) : Prop := M ≤ pStar

structure EqualityConstrainedOptimizationProblem where
  n : ℕ
  E : Type
  eq_constraints : Set E
  f : (Fin n → ℝ) → ℝ
  c : E → (Fin n → ℝ) → ℝ
  continuous_f : Continuous f
  continuous_c : ∀ i : E, Continuous (c i)

def EqualityConstrainedOptimizationProblem.isFeasible
    (p : EqualityConstrainedOptimizationProblem) (x : Fin p.n → ℝ) : Prop :=
  ∀ i ∈ p.eq_constraints, p.c i x = 0

def EqualityConstrainedOptimizationProblem.objectiveValue
    (p : EqualityConstrainedOptimizationProblem) (x : Fin p.n → ℝ) : ℝ :=
  p.f x

structure MorrisonMethod where
  problem : EqualityConstrainedOptimizationProblem
  v : ℝ → (Fin problem.n → ℝ) → ℝ
  M : ℕ → ℝ
  x : ℕ → Fin problem.n → ℝ
  x_is_argmin : ∀ k : ℕ, IsMinOn (v (M k)) Set.univ (x k)
  update_rule : ∀ k : ℕ, M (k + 1) = M k + Real.sqrt (v (M k) (x k))

def MorrisonMethod.stepValue (mm : MorrisonMethod) (k : ℕ) : ℝ :=
  mm.v (mm.M k) (mm.x k)

def MorrisonMethod.nextM (mm : MorrisonMethod) (k : ℕ) : ℝ :=
  mm.M k + Real.sqrt (mm.stepValue k)

theorem MorrisonMethod_nextM_le_optimal_of_current_le_optimal
    (mm : MorrisonMethod)
    (k : ℕ)
    (xStar : Fin mm.problem.n → ℝ)
    (hxStar_feasible : mm.problem.isFeasible xStar)
    (hv : ∀ M : ℝ, ∀ x : Fin mm.problem.n → ℝ,
      mm.v M x =
        (mm.problem.f x - M) ^ 2 +
          ∑' i, by
            classical
            exact if i ∈ mm.problem.eq_constraints then (mm.problem.c i x) ^ 2 else 0)
    (hMlb : IsLowerBoundEstimate (mm.problem.f xStar) (mm.M k)) :
    mm.nextM k ≤ mm.problem.f xStar := by
  sorry

end «CAM-Bench-769»
