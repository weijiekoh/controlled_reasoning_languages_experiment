import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-412»

def IsProperCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (0 ∈ K ∧ ∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  K ∩ {x | -x ∈ K} = {0} ∧
  Set.Nonempty (interior K)

def ConeOrder {n : ℕ} (K : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y - x ∈ K

def StrictConeOrder {n : ℕ} (K : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  y - x ∈ interior K

open scoped Topology

theorem gradient_mem_negative_dualCone_of_concave_log_homogeneous
    {n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsProperCone K) :
    ∀ (psi : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ),
      y ∈ -interior K →
      StrictConeOrder K y 0 →
      ConcaveOn ℝ (-interior K) psi →
      (∀ x : Fin n → ℝ, x ∈ -interior K → DifferentiableAt ℝ psi x) →
      (∀ x : Fin n → ℝ, x ∈ -interior K → ∀ s : ℝ, 0 < s → psi (s • x) = psi x + Real.log s) →
      ∀ x : Fin n → ℝ, x ∈ K → ∑ i, (fderiv ℝ psi y) (Pi.single i (1 : ℝ)) * x i ≤ 0 := by
  sorry

end «CAM-Bench-412»
