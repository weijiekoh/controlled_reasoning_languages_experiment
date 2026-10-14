import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-454»

def SupportsHyperplane {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (x0 a : EuclideanSpace ℝ (Fin n)) : Prop :=
  x0 ∈ C ∧ ∀ x, x ∈ C → ⟪a, x - x0⟫ ≤ 0

open scoped BigOperators

def convexHullOfPoints {n K : ℕ} (x : Fin K → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ l : Fin K → ℝ, (∀ i, 0 ≤ l i) ∧ (∑ i, l i) = 1 ∧ (∑ i, l i • x i) = y}

theorem polyhedralInner_outer_approximation
    {n K : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (x : Fin K → EuclideanSpace ℝ (Fin n))
    (hx_boundary : ∀ i, x i ∈ frontier C)
    (hx_mem : ∀ i, x i ∈ C)
    (a : Fin K → EuclideanSpace ℝ (Fin n))
    (h_supports : ∀ i, SupportsHyperplane C (x i) (a i)) :
    convexHullOfPoints x ⊆ C ∧
      C ⊆ {y : EuclideanSpace ℝ (Fin n) | ∀ i : Fin K, ⟪a i, y - x i⟫ ≤ 0} :=
by
  sorry

end «CAM-Bench-454»
