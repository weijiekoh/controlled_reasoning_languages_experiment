import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-698»

open scoped BigOperators

theorem dist_scaled_sets_translate_convex
    {n : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty)
    (hD_nonempty : D.Nonempty)
    (hC_convex : Convex ℝ C)
    (hD_convex : Convex ℝ D) :
    ConvexOn ℝ
      {p : EuclideanSpace ℝ (Fin n) × ℝ | 0 < p.2}
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        sInf
          {r : ℝ |
            ∃ a ∈ ((fun c : EuclideanSpace ℝ (Fin n) => p.2 • c) '' C),
              ∃ b ∈ ((fun d : EuclideanSpace ℝ (Fin n) => p.1 + p.2 • d) '' D),
                r = ‖a - b‖}) := by
  sorry

end «CAM-Bench-698»
