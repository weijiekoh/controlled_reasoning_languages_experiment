import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-509»

theorem top_r_abs_sum_convexOn
    (n r : ℕ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ n) :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        sSup (({s : Finset (Fin n) | s.card = r}).image (fun s => ∑ i, if i ∈ s then ‖x i‖ else 0))) := by
  sorry

end «CAM-Bench-509»
