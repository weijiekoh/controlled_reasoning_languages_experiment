import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-235»

open scoped BigOperators

def CoordinatewiseMonotone {k : ℕ} (h : (Fin k → ℝ) → ℝ) (i : Fin k) : Prop :=
  ∀ u v : Fin k → ℝ, (∀ j : Fin k, j ≠ i → u j = v j) → u i ≤ v i → h u ≤ h v

def CoordinatewiseAntitone {k : ℕ} (h : (Fin k → ℝ) → ℝ) (i : Fin k) : Prop :=
  ∀ u v : Fin k → ℝ, (∀ j : Fin k, j ≠ i → u j = v j) → u i ≤ v i → h v ≤ h u

theorem convex_of_convex_coordinatewise_monotone_comp
    {n k : ℕ}
    (h : (Fin k → ℝ) → ℝ)
    (g : Fin k → (Fin n → ℝ) → ℝ)
    (hh : ConvexOn ℝ Set.univ h)
    (hcond : ∀ i : Fin k,
      CoordinatewiseMonotone h i ∧ ConvexOn ℝ Set.univ (g i) ∨
      CoordinatewiseAntitone h i ∧ ConcaveOn ℝ Set.univ (g i) ∨
      (∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ x : Fin n → ℝ, g i x = ∑ j, a j * x j + b)) :
    ConvexOn ℝ Set.univ (fun x => h (fun i => g i x)) := by
  sorry

end «CAM-Bench-235»
