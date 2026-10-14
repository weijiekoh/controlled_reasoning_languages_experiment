import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-283»

def Pointed (C : Set (Fin (Nat.succ n) → ℝ)) : Prop :=
  C ∩ Neg.neg '' C = ({0} : Set (Fin (Nat.succ n) → ℝ))

structure ConvexOptimizationProblem where
  n : ℕ
  m : ℕ
  p : ℕ
  c : Fin n → ℝ
  A : Matrix (Fin p) (Fin n) ℝ
  b : Fin p → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ
  convex_f : ∀ i : Fin m, ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (f i)

def ConvexOptimizationProblem.isFeasible
    (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i : Fin P.m, P.f i x ≤ 0) ∧ P.A.mulVec x = P.b

def ConvexOptimizationProblem.objective
    (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

theorem K_pointed_of_bounded_feasible_set
    (P : ConvexOptimizationProblem)
    (hbounded :
      Bornology.IsBounded
        {x : Fin P.n → ℝ | P.isFeasible x}) :
    Pointed
      (closure
        {xt : Fin (Nat.succ P.n) → ℝ |
          0 < xt 0 ∧
          (∀ i : Fin P.m,
            xt 0 * P.f i
              (fun j : Fin P.n => xt (Fin.succ j) / xt 0) ≤ 0) ∧
          P.A.mulVec (fun j : Fin P.n => xt (Fin.succ j) / xt 0) = P.b}) := by
  sorry

end «CAM-Bench-283»
