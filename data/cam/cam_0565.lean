import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-565»

open scoped BigOperators

theorem log_polynomial_concave_on_interval
    (p : Polynomial ℝ)
    (hp : p ≠ 0)
    (hrealroots : p.Splits)
    (I : Set ℝ)
    (hI : Convex ℝ I)
    (hpos : ∀ x ∈ I, 0 < p.eval x) :
    ConcaveOn ℝ I (fun x => Real.log (p.eval x)) := by
  sorry

end «CAM-Bench-565»
