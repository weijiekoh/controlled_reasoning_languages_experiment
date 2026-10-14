import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-466»

def IsProperCone (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsClosed K ∧ (K ∩ (-K) = ({0} : Set (EuclideanSpace ℝ (Fin n)))) ∧
    (interior K).Nonempty

variable {n : ℕ}

theorem Kmplus_isProperCone :
    IsProperCone
      ({x : EuclideanSpace ℝ (Fin n) |
          (∀ i j : Fin n, i ≤ j → x i ≥ x j) ∧ (∀ i : Fin n, 0 ≤ x i)} : Set (EuclideanSpace ℝ (Fin n))) :=
by
  sorry

end «CAM-Bench-466»
