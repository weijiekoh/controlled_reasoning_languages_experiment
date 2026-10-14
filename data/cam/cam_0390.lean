import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-390»

structure FilterLengthIntegerOptimization where
  F : (N : ℕ) → Set (Fin (N + 1) → ℝ)

def FilterLengthIntegerOptimization.objectiveSet (p : FilterLengthIntegerOptimization) : Set ℕ :=
  {N | (p.F N).Nonempty}

def FilterLengthIntegerOptimization.is_feasible (p : FilterLengthIntegerOptimization) (N : ℕ) : Prop :=
  (p.F N).Nonempty

def FilterLengthIntegerOptimization.is_optimal (p : FilterLengthIntegerOptimization) (N : ℕ) : Prop :=
  p.is_feasible N ∧ ∀ M : ℕ, p.is_feasible M → N ≤ M

theorem fir_filter_design_equivalent_to_filter_length_integer_optimization_and_convex_feasibility
    (ωc α : ℝ)
    (hωc : ωc ∈ Set.Icc (0 : ℝ) Real.pi)
    (hα : 0 ≤ α) :
    ∃ p : FilterLengthIntegerOptimization,
      (∀ N : ℕ,
        p.F N =
          {a : Fin (N + 1) → ℝ |
            (∀ ω : ℝ,
              ω ∈ Set.Icc (0 : ℝ) (Real.pi / 3) →
                0.89 ≤
                    a 0 + ∑ k : Fin N, a k.succ * Real.cos (((k : ℕ) + 1 : ℕ) * ω)
                  ∧
                    a 0 + ∑ k : Fin N, a k.succ * Real.cos (((k : ℕ) + 1 : ℕ) * ω) ≤ 1.12)
              ∧
                ∀ ω : ℝ,
                    ω ∈ Set.Icc ωc Real.pi →
                      |a 0 + ∑ k : Fin N, a k.succ * Real.cos (((k : ℕ) + 1 : ℕ) * ω)| ≤ α}) ∧
        (∀ N : ℕ,
          Convex ℝ (p.F N)) := by
  sorry

end «CAM-Bench-390»
