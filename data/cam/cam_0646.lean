import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-646»

theorem exists_monotone_nondecreasing_interpolant_iff
    {k m : ℕ} (u : Fin m → Fin k → ℝ) (y : Fin m → ℝ) :
    (∃ f : (Fin k → ℝ) → ℝ,
      (∀ a b : Fin k → ℝ, (∀ l : Fin k, a l ≥ b l) → f a ≥ f b) ∧
      ∀ i : Fin m, f (u i) = y i) ↔
    ∀ i j : Fin m, (∀ l : Fin k, u i l ≥ u j l) → y i ≥ y j := by
  sorry

end «CAM-Bench-646»
