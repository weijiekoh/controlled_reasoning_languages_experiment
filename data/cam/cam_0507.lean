import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-507»

open Matrix

theorem trace_inv_matrix_affine_convexOn
    {m n : ℕ}
    (A : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, IsSymm (A i)) :
    let domf : Set (Fin n → ℝ) := {x : Fin n → ℝ | PosDef (A 0 + ∑ i : Fin n, (x i) • A i.succ)}
    let f : (Fin n → ℝ) → ℝ :=
      fun x => Matrix.trace ((A 0 + ∑ i : Fin n, (x i) • A i.succ)⁻¹)
    ConvexOn ℝ domf f := by
  sorry

end «CAM-Bench-507»
