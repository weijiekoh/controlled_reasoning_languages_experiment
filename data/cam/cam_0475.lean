import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-475»

def barrierCone {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  { y | BddAbove ((fun x => ⟪y, x⟫) '' C) }

def supportFunction {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => ⟪y, x⟫) '' C)

def IsConvexCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧
    (∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K)

open scoped RealInnerProductSpace

theorem barrierCone_supportFunction_sublinear
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCne : C.Nonempty) :
    IsConvexCone (barrierCone (n := n) C) ∧
      (∀ y ∈ barrierCone (n := n) C, ∀ z ∈ barrierCone (n := n) C,
        y + z ∈ barrierCone (n := n) C ∧
          supportFunction C (y + z) ≤ supportFunction C y + supportFunction C z) ∧
      (∀ y ∈ barrierCone (n := n) C, ∀ a : ℝ, 0 ≤ a →
        a • y ∈ barrierCone (n := n) C ∧
          supportFunction C (a • y) = a * supportFunction C y) := by
  sorry

end «CAM-Bench-475»
