import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-767»

def logarithmicPenaltyFunction
    {ι X : Type*}
    (f : X → ℝ)
    (c : ι → X → ℝ)
    (σ : ℝ)
    (s : Finset ι)
    (x : X) : ℝ :=
  if 0 < σ ∧ ∀ i ∈ s, c i x < 0 then
    f x - σ * Finset.sum s (fun i => Real.log (-c i x))
  else
    0

structure InequalityConstrainedOptimizationProblem (ι X : Type*) where
  objective : X → ℝ
  constraint : ι → X → ℝ

noncomputable def InequalityConstrainedOptimizationProblem.activeSet
    {ι X : Type*}
    (P : InequalityConstrainedOptimizationProblem ι X) : Finset ι := by
  classical
  by_cases h : Finite ι
  · exact @Finset.univ ι (Fintype.ofFinite ι)
  · exact ∅

def InequalityConstrainedOptimizationProblem.isFeasible
    {ι X : Type*}
    (P : InequalityConstrainedOptimizationProblem ι X) (x : X) : Prop :=
  ∀ i : ι, P.constraint i x ≤ 0

def InequalityConstrainedOptimizationProblem.isInteriorPoint
    {ι X : Type*}
    (P : InequalityConstrainedOptimizationProblem ι X) (x : X) : Prop :=
  ∀ i : ι, P.constraint i x < 0

def InequalityConstrainedOptimizationProblem.feasibleSet
    {ι X : Type*}
    (P : InequalityConstrainedOptimizationProblem ι X) : Set X :=
  {x | P.isFeasible x}

def InequalityConstrainedOptimizationProblem.interior
    {ι X : Type*}
    (P : InequalityConstrainedOptimizationProblem ι X) : Set X :=
  {x | P.isInteriorPoint x}

def InequalityConstrainedOptimizationProblem.logarithmicPenalty
    {ι X : Type*}
    (P : InequalityConstrainedOptimizationProblem ι X)
    (σ : ℝ) (x : X) : ℝ :=
  logarithmicPenaltyFunction P.objective P.constraint σ P.activeSet x

def HasInfimumValueOnSet
    {X : Type*} (s : Set X) (f : X → ℝ) (value : ℝ) : Prop :=
  (∀ x ∈ s, value ≤ f x) ∧
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ s, f x < value + ε

structure LogarithmicPenaltyFunctionMethod (ι X : Type*) where
  problem : InequalityConstrainedOptimizationProblem ι X
  ρ : ℝ
  σ : ℕ → ℝ
  x : ℕ → X
  subproblemSolver : ℕ → X → X

def LogarithmicPenaltyFunctionMethod.subproblemObjective
    {ι X : Type*}
    (M : LogarithmicPenaltyFunctionMethod ι X) (k : ℕ) : X → ℝ :=
  fun y => M.problem.logarithmicPenalty (M.σ k) y

def LogarithmicPenaltyFunctionMethod.GlobalMinimizerStep
    {ι X : Type*}
    (M : LogarithmicPenaltyFunctionMethod ι X) : Prop :=
  ∀ k : ℕ, IsMinOn (M.subproblemObjective k) Set.univ (M.x (k + 1))

theorem logarithmicPenaltyMethod_terminates_or_converges
    {ι X : Type*} [DecidableEq ι]
    (M : LogarithmicPenaltyFunctionMethod ι X)
    (interiorInf : ℝ)
    (hρpos : 0 < M.ρ)
    (hρlt : M.ρ < 1)
    (hσrec : ∀ k : ℕ, M.σ (k + 1) = M.ρ * M.σ k)
    (hσpos : ∀ k : ℕ, 0 < M.σ k)
    (hstep_initial :
      ∀ k : ℕ, M.subproblemSolver k (M.x k) = M.x (k + 1))
    (hglobal_minimizer_step : M.GlobalMinimizerStep)
    (hInterior : ∀ k : ℕ, M.problem.isInteriorPoint (M.x (k + 1)))
    (hInteriorInf :
      HasInfimumValueOnSet M.problem.interior M.problem.objective interiorInf)
    (h_bdd_below :
      BddBelow (M.problem.objective '' M.problem.feasibleSet))
    :
    (∃ N : ℕ, ∀ k : ℕ, N ≤ k → M.x (k + 1) = M.x k) ∨
      (Tendsto
          (fun k : ℕ =>
            M.σ k *
              Finset.sum M.problem.activeSet
                (fun i => Real.log (-M.problem.constraint i (M.x (k + 1)))))
          atTop (𝓝 0) ∧
        Tendsto
          (fun k : ℕ => M.problem.objective (M.x k))
          atTop
          (𝓝 interiorInf)) := by
  sorry

end «CAM-Bench-767»
