import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-272»

def IsDifferentiableConvexFunction (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Differentiable ℝ f ∧
    ∀ x y : EuclideanSpace ℝ (Fin n),
      f y ≥ f x + fderiv ℝ f x (y - x)

def allOnesVector : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun _ => (1 : ℝ))

def standardSimplex : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∑ i : Fin n, x i = (1 : ℝ) ∧ ∀ i : Fin n, 0 ≤ x i}

theorem minimizer_on_standardSimplex_iff_gradient_coordinates_ge_average
    (n : ℕ) (hn : 1 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsDifferentiableConvexFunction f)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ standardSimplex) :
    (∀ y ∈ standardSimplex, f x ≤ f y) ↔
      ∀ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1) ≥ fderiv ℝ f x x := by
  sorry

end «CAM-Bench-272»
