import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-379»

theorem diag_mul_diag_eq_iff_hadamardSquare_mul_eq
    {n : Type} [Fintype n] [DecidableEq n]
    (X C : Matrix n n ℝ) (hX : X.IsSymm) (hC : C.IsSymm) (w : n → ℝ) :
    let D : Matrix n n ℝ := Matrix.diagonal w
    Matrix.diag (X * D * X) = (fun i => (1 : ℝ) - Matrix.diag (X * C * X) i) ↔
      (fun i => ∑ j, (X i j) ^ 2 * w j) = (fun i => (1 : ℝ) - Matrix.diag (X * C * X) i) := by
  sorry

end «CAM-Bench-379»
