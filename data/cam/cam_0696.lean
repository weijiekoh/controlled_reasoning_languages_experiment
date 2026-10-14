import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-696»

theorem signedDistToConvexSet_convex
    {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n)))
    [DecidablePred fun x : EuclideanSpace ℝ (Fin n) => x ∈ C]
    (hC_nonempty : C.Nonempty)
    (hC_compl_nonempty : Cᶜ.Nonempty)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    let s : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x =>
        if hx : x ∈ C then
          -sInf {r : ℝ | ∃ y ∈ Cᶜ, r = ‖x - y‖}
        else
          sInf {r : ℝ | ∃ y ∈ C, r = ‖x - y‖}
    ConvexOn ℝ Set.univ s := by
  sorry

end «CAM-Bench-696»
