import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-539»

open scoped BigOperators
open scoped RealInnerProductSpace

def supportFunction {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun y => sSup ((fun x : EuclideanSpace ℝ (Fin n) => (⟪y, x⟫ : ℝ)) '' C)

theorem supportFunction_eq_supportFunction_convexHull {n : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin n))) :
    supportFunction B = supportFunction (convexHull ℝ B) := by
  sorry

end «CAM-Bench-539»
