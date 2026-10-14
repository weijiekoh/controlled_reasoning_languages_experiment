import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-577»

def IsProperConvexCone (K : Set (Fin m → ℝ)) : Prop :=
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Fin m → ℝ⦄, x ∈ K → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  Set.Nonempty (interior K) ∧
  K ∩ {x | -x ∈ K} = {0}

def GeneralizedInequality (K : Set (Fin m → ℝ)) (y z : Fin m → ℝ) : Prop :=
  z - y ∈ K

def KEpigraph (K : Set (Fin m → ℝ)) (f : (Fin n → ℝ) → Fin m → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | GeneralizedInequality K (f p.1) p.2}

def IsKConvex (K : Set (Fin m → ℝ)) (f : (Fin n → ℝ) → Fin m → ℝ) : Prop :=
  ∀ ⦃x y : Fin n → ℝ⦄, ∀ ⦃θ : ℝ⦄,
    0 ≤ θ → θ ≤ 1 →
      GeneralizedInequality K
        (f (θ • x + (1 - θ) • y))
        (θ • f x + (1 - θ) • f y)

theorem isKConvex_iff_convex_KEpigraph
    {K : Set (Fin m → ℝ)} {f : (Fin n → ℝ) → Fin m → ℝ}
    (hK : IsProperConvexCone K) :
    IsKConvex K f ↔ Convex ℝ (KEpigraph K f) := by
  sorry

end «CAM-Bench-577»
