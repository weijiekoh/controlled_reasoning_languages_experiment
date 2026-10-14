import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-154»

theorem polynomialCoefficientSet_convex
    (k : ℕ) (hk : 1 ≤ k) (α β : ℝ) (hαβ : α ≤ β) :
    Convex ℝ
      {a : Fin k → ℝ |
        (a ⟨0, hk⟩ = 1) ∧
        ∀ t ∈ Set.Icc α β,
          |∑ i : Fin k, a i * t ^ (i : ℕ)| ≤ 1} := by
  sorry

end «CAM-Bench-154»
