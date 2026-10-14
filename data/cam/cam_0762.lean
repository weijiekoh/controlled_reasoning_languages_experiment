import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-762»

def HasConvergenceRateOrder
    (e h : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → e K ≤ C * h K

def IsWorstCaseBound
    {P : Type}
    (ProbSet : Set P)
    (e : ℕ → P → ℝ)
    (w : ℕ → ℝ) : Prop :=
  ∀ K : ℕ,
    (∀ P ∈ ProbSet, e K P ≤ w K) ∧
      ∀ r : ℝ, (∀ P ∈ ProbSet, e K P ≤ r) → w K ≤ r

theorem subgradient_method_worst_case_rate_not_improvable
    (Problem : Type)
    (ProbSet : Set Problem)
    (e : ℕ → Problem → ℝ)
    (w : ℕ → ℝ)
    (G R : ℝ)
    (hG : 0 < G)
    (hR : 0 < R)
    (hw : IsWorstCaseBound ProbSet e w)
    (hLower :
      ∀ K : ℕ, ∃ P ∈ ProbSet, e K P ≥ (G * R) / (1 + Real.sqrt K))
    : ∀ h : ℕ → ℝ, HasConvergenceRateOrder w h →
        ∃ c > 0, ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → c * ((G * R) / (1 + Real.sqrt K)) ≤ h K := by
  sorry

end «CAM-Bench-762»
