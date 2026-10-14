import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-267»

theorem perspective_of_convex_is_convex
    {n : ℕ} {s t : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → ℝ}
    (hf : ConvexOn ℝ s f) (hf0 : (0 : Fin n → ℝ) ∈ s) (h0 : f 0 ≤ 0)
    (hg : ConcaveOn ℝ t g) (hg_pos : ∀ x ∈ t, 0 < g x) :
    ConvexOn ℝ {x | x ∈ t ∧ (g x)⁻¹ • x ∈ s} (fun x => g x * f ((g x)⁻¹ • x)) := by
  sorry

end «CAM-Bench-267»
