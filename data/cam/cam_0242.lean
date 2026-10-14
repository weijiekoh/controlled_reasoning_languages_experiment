import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-242»

theorem matrix_inverse_quadratic_form_not_convex_counterexample :
    ¬ ConvexOn ℝ
      { p : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) |
        ∀ z : Fin 2 → ℝ, z ≠ 0 →
          0 < dotProduct z (((p.1 + p.1.transpose).mulVec z)) }
      (fun p => dotProduct p.2 (p.1⁻¹.mulVec p.2)) ∧
    ((!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ), (![1, 0] : Fin 2 → ℝ)) ∈
      { p : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) |
        ∀ z : Fin 2 → ℝ, z ≠ 0 →
          0 < dotProduct z (((p.1 + p.1.transpose).mulVec z)) } ∧
    ((!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ), (![1, 0] : Fin 2 → ℝ)) ∈
      { p : Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) |
        ∀ z : Fin 2 → ℝ, z ≠ 0 →
          0 < dotProduct z (((p.1 + p.1.transpose).mulVec z)) } ∧
    (dotProduct (![1, 0] : Fin 2 → ℝ)
      (((!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹).mulVec (![1, 0] : Fin 2 → ℝ))) = (1 : ℝ) / 2 ∧
    (dotProduct (![1, 0] : Fin 2 → ℝ)
      (((!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹).mulVec (![1, 0] : Fin 2 → ℝ))) = (1 : ℝ) / 2 ∧
    (((!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
        (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ)) / 2 =
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (((![1, 0] : Fin 2 → ℝ) + (![1, 0] : Fin 2 → ℝ)) / 2 = (![1, 0] : Fin 2 → ℝ)) ∧
    dotProduct (![1, 0] : Fin 2 → ℝ)
      (((((!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) +
          (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ)) / 2)⁻¹).mulVec
        (((![1, 0] : Fin 2 → ℝ) + (![1, 0] : Fin 2 → ℝ)) / 2)) = 1 ∧
    1 >
      (1 / 2 : ℝ) *
        ((dotProduct (![1, 0] : Fin 2 → ℝ)
            (((!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹).mulVec (![1, 0] : Fin 2 → ℝ))) +
          (dotProduct (![1, 0] : Fin 2 → ℝ)
            (((!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹).mulVec (![1, 0] : Fin 2 → ℝ)))) := by
  sorry

end «CAM-Bench-242»
