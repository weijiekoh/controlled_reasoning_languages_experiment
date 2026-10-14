import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-224»

open scoped BigOperators

theorem sup_eq_max_of_convexOn_convexHull_finset
    {n : ℕ} {k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ (convexHull ℝ (Set.range v)) f) :
    sSup (f '' convexHull ℝ (Set.range v)) = ⨆ i : Fin k, f (v i) := by
  sorry

end «CAM-Bench-224»
