import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-342»

open scoped BigOperators

structure MaximumEntropyProblem where
  N : ℕ
  n : ℕ
  hN : 1 ≤ N
  x : Fin N → (Fin n → ℝ)
  μ : Fin n → ℝ

def MaximumEntropyProblem.entropyTerm (t : ℝ) : ℝ :=
  if t = 0 then 0 else -t * Real.log t

def MaximumEntropyProblem.objective (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : ℝ :=
  ∑ i, MaximumEntropyProblem.entropyTerm (π i)

def MaximumEntropyProblem.IsFeasible (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧
    (∑ i, π i = 1) ∧
      ∀ j, ∑ i, π i * P.x i j = P.μ j

def MaximumEntropyProblem.IsOptimal (P : MaximumEntropyProblem) (π : Fin P.N → ℝ) : Prop :=
  P.IsFeasible π ∧
    ∀ π', P.IsFeasible π' → P.objective π' ≤ P.objective π

theorem maximumEntropyProblem_is_convexOptimizationProblem
    (P : MaximumEntropyProblem) :
    ConcaveOn ℝ {π : Fin P.N → ℝ | ∀ i, 0 ≤ π i} P.objective ∧
      Convex ℝ {π : Fin P.N → ℝ | P.IsFeasible π} := by
  sorry

end «CAM-Bench-342»
