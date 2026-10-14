import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-596»

structure LinearOptimizationOverEllipsoid (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  A_symm : A.IsSymm
  A_posDef : A.PosDef
  xc : Fin n → ℝ
  c : Fin n → ℝ
  c_nonzero : c ≠ 0

def LinearOptimizationOverEllipsoid.objective {n : ℕ}
    (P : LinearOptimizationOverEllipsoid n) (x : Fin n → ℝ) : ℝ :=
  dotProduct P.c x

def LinearOptimizationOverEllipsoid.isFeasible {n : ℕ}
    (P : LinearOptimizationOverEllipsoid n) (x : Fin n → ℝ) : Prop :=
  dotProduct (x - P.xc) (P.A.mulVec (x - P.xc)) ≤ 1

theorem linearOptimizationOverEllipsoid_unique_optimum
    {n : ℕ} (P : LinearOptimizationOverEllipsoid n) :
    let q := dotProduct P.c (((P.A)⁻¹).mulVec P.c)
    let xStar := P.xc - (1 / Real.sqrt q) • (((P.A)⁻¹).mulVec P.c)
    P.isFeasible xStar ∧
      P.objective xStar = dotProduct P.c P.xc - Real.sqrt q ∧
      ∀ x, P.isFeasible x →
        P.objective xStar ≤ P.objective x ∧
          (P.objective x = P.objective xStar → x = xStar) := by
  sorry

end «CAM-Bench-596»
