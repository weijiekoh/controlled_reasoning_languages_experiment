import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-427»

theorem slab_convex (a : EuclideanSpace ℝ (Fin n)) (α β : ℝ) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin n) | α ≤ ⟪a, x⟫ ∧ ⟪a, x⟫ ≤ β} := by
  sorry

end «CAM-Bench-427»
