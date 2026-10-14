import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-647»

open scoped BigOperators

theorem convex_monotone_nondecreasing_interpolation_iff
    {k m : ℕ} (u : Fin m → Fin k → ℝ) (y : Fin m → ℝ) :
    (∃ f : (Fin k → ℝ) → ℝ,
      ConvexOn ℝ Set.univ f ∧
      (∀ u v : Fin k → ℝ, (∀ l : Fin k, v l ≤ u l) → f v ≤ f u) ∧
      ∀ i : Fin m, f (u i) = y i) ↔
    ∃ g : Fin m → Fin k → ℝ,
      (∀ i : Fin m, ∀ l : Fin k, 0 ≤ g i l) ∧
      ∀ i j : Fin m, y j ≥ y i + ∑ l : Fin k, g i l * (u j l - u i l) := by
  sorry

end «CAM-Bench-647»
