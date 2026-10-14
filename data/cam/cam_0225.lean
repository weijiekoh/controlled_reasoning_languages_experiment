import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-225»

def weightedGeometricMean (n : ℕ) (α x : Fin n → ℝ) : ℝ :=
  ∏ k, x k ^ (α k)

theorem weightedGeometricMean_concaveOn_pos
    (n : ℕ) (α : Fin n → ℝ)
    (hα_nonneg : ∀ k, 0 ≤ α k)
    (hα_sum : ∑ k, α k ≤ 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ k, 0 < x k} (weightedGeometricMean n α) := by
  sorry

end «CAM-Bench-225»
