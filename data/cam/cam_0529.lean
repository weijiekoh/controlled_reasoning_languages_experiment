import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-529»

open scoped Convex

theorem convex_underestimator_le_infConvEpigraph
    {n : ℕ} (f g : (Fin n → ℝ) → ℝ)
    (hfiber_nonempty :
      ∀ x, {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈ convexHull ℝ {p | f p.1 ≤ p.2}}.Nonempty)
    (hfiber_bddBelow :
      ∀ x, BddBelow {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈ convexHull ℝ {p | f p.1 ≤ p.2}})
    (hg :
      ∀ x,
        g x =
          sInf {t : ℝ | ((x, t) : (Fin n → ℝ) × ℝ) ∈ convexHull ℝ {p | f p.1 ≤ p.2}}) :
    ConvexOn ℝ Set.univ g ∧
      (∀ x, g x ≤ f x) ∧
      (∀ h : (Fin n → ℝ) → ℝ, ConvexOn ℝ Set.univ h → (∀ x, h x ≤ f x) → ∀ x, h x ≤ g x) := by
  sorry

end «CAM-Bench-529»
