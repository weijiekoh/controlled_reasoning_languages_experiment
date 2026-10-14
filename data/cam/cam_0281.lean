import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-281»

structure ConvexOptimizationProblem where
  n : ℕ
  p : ℕ
  m : ℕ
  c : Fin n → ℝ
  A : Fin p → Fin n → ℝ
  b : Fin p → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ
  convex_f : ∀ i : Fin m, ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (f i)

def ConvexOptimizationProblem.isFeasible (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.m, P.f i x ≤ 0) ∧ ∀ j : Fin P.p, ∑ k : Fin P.n, P.A j k * x k = P.b j

def ConvexOptimizationProblem.objective (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ k : Fin P.n, P.c k * x k

theorem convexConeLiftSet_is_convex_cone (P : ConvexOptimizationProblem) :
    let K : Set ((Fin P.n → ℝ) × ℝ) :=
      closure
        {xt : (Fin P.n → ℝ) × ℝ |
          0 < xt.2 ∧ ∀ i : Fin P.m, xt.2 * P.f i (fun k => xt.1 k / xt.2) ≤ 0}
    Convex ℝ K ∧
      ∀ ⦃z : (Fin P.n → ℝ) × ℝ⦄, z ∈ K → ∀ a : ℝ, 0 ≤ a → a • z ∈ K := by
  sorry

end «CAM-Bench-281»
