import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-500»

theorem det_rpow_one_div_concave_on_posDef
    (n : ℕ) (hn : 1 ≤ n) :
    ConcaveOn ℝ
      {X : Matrix (Fin n) (Fin n) ℝ | X.PosDef}
      (fun X => (Matrix.det X) ^ (1 / (n : ℝ))) := by
  sorry

end «CAM-Bench-500»
