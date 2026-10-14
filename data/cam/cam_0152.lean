import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-152»

open scoped RealInnerProductSpace

theorem kappa_standard_basis_directions_eq_inv_sqrt
    (n : ℕ) (hn : 1 ≤ n) :
    let Dk : Set (EuclideanSpace ℝ (Fin n)) :=
      {p | ∃ i : Fin n, p = (fun j => if j = i then (1 : ℝ) else 0) ∨
          p = -(fun j => if j = i then (1 : ℝ) else 0)}
    let kappa : Set (EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun D =>
        sInf
          {r : ℝ |
            ∃ v : EuclideanSpace ℝ (Fin n),
              v ≠ 0 ∧
              r = sSup {s : ℝ |
                ∃ p : EuclideanSpace ℝ (Fin n),
                  p ∈ D ∧ p ≠ 0 ∧
                  s = ⟪v, p⟫ / (‖v‖ * ‖p‖)}}
    kappa Dk = (1 / Real.sqrt n : ℝ) := by
  sorry

end «CAM-Bench-152»
