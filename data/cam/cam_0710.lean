import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-710»

theorem convex_iff_convex_epigraph {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    C.Nonempty →
    Convex ℝ C →
      (ConvexOn ℝ C f ↔
        Convex ℝ {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ C ∧ f p.1 ≤ p.2}) := by
  sorry

end «CAM-Bench-710»
