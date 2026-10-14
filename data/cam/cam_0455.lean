import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-455»

open scoped RealInnerProductSpace

def supportFunction {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EReal :=
  fun y => sSup (((fun x : EuclideanSpace ℝ (Fin n) => ((⟪y, x⟫ : ℝ) : EReal)) '' E))

theorem closed_convex_eq_iff_supportFunction_eq
    {n : ℕ} {C D : Set (EuclideanSpace ℝ (Fin n))}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    C = D ↔ supportFunction C = supportFunction D := by
  sorry

end «CAM-Bench-455»
