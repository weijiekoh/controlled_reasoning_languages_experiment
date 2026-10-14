import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-479»

theorem convexHull_eq_sInter_convex_supersets
    (n : ℕ) (S : Set (EuclideanSpace ℝ (Fin n))) :
    convexHull ℝ S = ⋂₀ {C : Set (EuclideanSpace ℝ (Fin n)) | S ⊆ C ∧ Convex ℝ C} := by
  sorry

end «CAM-Bench-479»
