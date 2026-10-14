import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-383»

theorem arithmetic_mean_ge_harmonic_mean
    (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : ∀ k : Fin n, 0 < x k) :
    (1 : ℝ) / n * ∑ k : Fin n, x k ≥
      ((1 : ℝ) / n * ∑ k : Fin n, (x k)⁻¹)⁻¹ := by
  sorry

end «CAM-Bench-383»
