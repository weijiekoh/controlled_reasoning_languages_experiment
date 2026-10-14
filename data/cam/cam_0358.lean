import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-358»

theorem ellipsoid_subset_strip_polyhedron_iff
    {n p : ℕ}
    (a : Fin p → EuclideanSpace ℝ (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ_symm : Q.IsSymm)
    (hQ_pos_def : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < ⟪x, (Matrix.toEuclideanLin Q) x⟫)
    :
    ({x : EuclideanSpace ℝ (Fin n) |
        ⟪x, (Matrix.toEuclideanLin Q⁻¹) x⟫ ≤ (1 : ℝ)} ⊆
      {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin p, -1 ≤ ⟪a i, x⟫ ∧ ⟪a i, x⟫ ≤ 1}) ↔
    (∀ i : Fin p, ⟪a i, (Matrix.toEuclideanLin Q) (a i)⟫ ≤ (1 : ℝ)) := by
  sorry

end «CAM-Bench-358»
