import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-499»

theorem trace_inv_convexOn_posDef
    (n : Type) [Fintype n] [DecidableEq n] :
    ConvexOn ℝ
      {X : Matrix n n ℝ | X.IsSymm ∧ X.PosDef}
      (fun X => Matrix.trace X⁻¹) := by
  sorry

end «CAM-Bench-499»
