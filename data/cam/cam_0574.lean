import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-574»

def MatrixConvex
    (f : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ ⦃X : Matrix (Fin n) (Fin n) ℝ⦄, X.PosDef → (f X).IsSymm) ∧
  ∀ ⦃X Y : Matrix (Fin n) (Fin n) ℝ⦄,
    X.PosDef → Y.PosDef →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      (θ • f X + (1 - θ) • f Y - f (θ • X + (1 - θ) • Y)).PosSemidef

theorem inverse_matrixConvex {n : ℕ} :
    MatrixConvex (fun X : Matrix (Fin n) (Fin n) ℝ => X⁻¹) := by
  sorry

end «CAM-Bench-574»
