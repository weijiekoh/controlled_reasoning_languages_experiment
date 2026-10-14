import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-413»

abbrev ProperConeSet {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  K ∩ (-K) = ({0} : Set (EuclideanSpace ℝ (Fin n))) ∧
  Set.Nonempty (interior K)

abbrev ConeSolid {n : ℕ} (K : ProperCone ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ProperConeSet (K : Set (EuclideanSpace ℝ (Fin n)))

def IsLogarithmicallyHomogeneous {n : ℕ}
    (K : ProperCone ℝ (EuclideanSpace ℝ (Fin n)))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (θ : ℝ) : Prop :=
  ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))) →
    ∀ ⦃s : ℝ⦄, 0 < s → ψ (s • x) = ψ x + θ * Real.log s

theorem gradient_scales_of_logarithmic_homogeneity
    {n : ℕ}
    {K : ProperCone ℝ (EuclideanSpace ℝ (Fin n))}
    {θ : ℝ}
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄,
      x ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))) →
      ∀ ⦃s : ℝ⦄, 0 < s → ψ (s • x) = ψ x + θ * Real.log s)
    (hdiff : ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄,
      x ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))) →
      DifferentiableAt ℝ ψ x)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ interior (K : Set (EuclideanSpace ℝ (Fin n))))
    {s : ℝ} (hs : 0 < s) :
    fderiv ℝ ψ (s • y) = (1 / s) • fderiv ℝ ψ y := by
  sorry

end «CAM-Bench-413»
