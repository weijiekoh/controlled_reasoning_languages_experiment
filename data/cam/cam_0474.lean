import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-474»

open scoped RealInnerProductSpace

def barrierCone {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  { y | BddAbove ((fun x => ⟪y, x⟫) '' C) }

def recessionCone {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  { y | ∀ ⦃x⦄, x ∈ C → ∀ ⦃t : ℝ⦄, 0 ≤ t → x - t • y ∈ C }

def IsCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • y ∈ K

def IsConvexCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCone (n := n) K

def dualCone {n : ℕ} (B : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  { y | ∀ z, z ∈ B → 0 ≤ ⟪z, y⟫ }

def normalCone (C : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ x, x ∈ C → dotProduct y (x - x₀) ≤ 0}

def activeSet {m : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) :
    Set (Fin m) :=
  {i | dotProduct (a i) x₀ = b i}

def polyhedron {m : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, dotProduct (A i) x ≤ b i}

def IsConvexConeFn {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  Convex ℝ K ∧
    ∀ ⦃y : Fin n → ℝ⦄, y ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • y ∈ K

theorem exercise_2_38_cone_characterizations
    {n m : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n)))
    (hDne : D.Nonempty) (hDcl : IsClosed D) (hDconv : Convex ℝ D)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x₀ : Fin n → ℝ) :
    IsConvexCone (barrierCone (n := n) C) ∧
    IsConvexCone (recessionCone (n := n) D) ∧
    recessionCone (n := n) D = dualCone (barrierCone (n := n) D) ∧
    IsConvexConeFn (normalCone (polyhedron A b) x₀) ∧
    (x₀ ∈ frontier (polyhedron A b) →
      normalCone (polyhedron A b) x₀ =
        {y | ∃ μ : Fin m → ℝ,
          (∀ i, 0 ≤ μ i) ∧
          (∀ i, i ∉ activeSet A b x₀ → μ i = 0) ∧
          y = ∑ i, (μ i) • (A i)}) := by
  sorry

end «CAM-Bench-474»
