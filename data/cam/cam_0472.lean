import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-472»

def IsCone (K : Set (Fin n → ℝ)) : Prop :=
  ∀ ⦃x : Fin n → ℝ⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K

def IsProperCone (K : Set (Fin n → ℝ)) : Prop :=
  IsCone (n := n) K ∧
    Convex ℝ K ∧
    IsClosed K ∧
    (interior K).Nonempty ∧
    K ∩ (-K) = ({0} : Set (Fin n → ℝ))

variable {k : ℕ}

theorem Kpol_isProperCone :
    let Kpol : Set (Fin (2 * k + 1) → ℝ) :=
      {x | ∀ t : ℝ, (∑ i : Fin (2 * k + 1), x i * t ^ (i.1 : ℕ)) ≥ 0}
    IsProperCone (n := 2 * k + 1) Kpol := by
  sorry

end «CAM-Bench-472»
