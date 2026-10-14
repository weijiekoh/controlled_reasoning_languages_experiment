import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-310»

theorem kyFan_r_convex_on_symmetric_matrices
    {n r : ℕ}
    (hr1 : 1 ≤ r)
    (hrn : r ≤ n) :
    ConvexOn ℝ
      {A : Matrix (Fin n) (Fin n) ℝ | A.IsSymm}
      (fun A =>
        sSup
          {s : ℝ | ∃ U : Matrix (Fin n) (Fin r) ℝ,
              U.transpose * U = 1 ∧
              s = Matrix.trace (U.transpose * A * U)}) := by
  sorry

end «CAM-Bench-310»
