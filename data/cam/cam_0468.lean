import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-468»

def IsProperCone (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ K → a • x ∈ K) ∧
    Convex ℝ K ∧
      IsClosed K ∧
        (interior K).Nonempty ∧
          ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄, x ∈ K → -x ∈ K → x = 0

def IsSolid (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  (interior K).Nonempty

def IsPointed (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  K ∩ (-K) = ({0} : Set (EuclideanSpace ℝ (Fin n)))

theorem lexCone_isCone_but_not_proper (n : ℕ) (hn : 0 < n) :
    let Klex : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | x = 0 ∨ ∃ k : Fin n, (∀ i : Fin n, i < k → x i = 0) ∧ 0 < x k}
    (∀ ⦃x y : EuclideanSpace ℝ (Fin n)⦄, x ∈ Klex → y ∈ Klex →
      ∀ ⦃α β : ℝ⦄, 0 ≤ α → 0 ≤ β → α • x + β • y ∈ Klex) ∧
      ¬ IsProperCone n Klex := by
  sorry

end «CAM-Bench-468»
