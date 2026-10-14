import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-317»

structure RobustLinearObjectiveProblem (n m : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  C : Set (Fin n → ℝ)
  C_nonempty : C.Nonempty
  feasible_exists : ∃ x : Fin n → ℝ, ∀ i : Fin m, b i ≤ (A.mulVec x) i

def RobustLinearObjectiveProblem.isFeasible
    {n m : ℕ} (p : RobustLinearObjectiveProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin m, p.b i ≤ (p.A.mulVec x) i

def RobustLinearObjectiveProblem.objective
    {n m : ℕ} (p : RobustLinearObjectiveProblem n m) (x : Fin n → ℝ) : ℝ :=
  sSup ((fun c : Fin n → ℝ => dotProduct c x) '' p.C)

theorem robustLinearObjectiveProblem_objective_convex
    {n m p : ℕ} (P : RobustLinearObjectiveProblem n m)
    (F : Matrix (Fin p) (Fin n) ℝ) (g : Fin p → ℝ)
    (hC : P.C = {c : Fin n → ℝ | ∀ i : Fin p, (F.mulVec c) i ≤ g i}) :
    ∀ x y : Fin n → ℝ, ∀ θ : ℝ,
      0 ≤ θ → θ ≤ 1 →
      sSup ((fun c : Fin n → ℝ =>
        ((dotProduct c (θ • x + (1 - θ) • y) : ℝ) : EReal)) '' P.C) ≤
        (θ : EReal) * sSup ((fun c : Fin n → ℝ =>
          ((dotProduct c x : ℝ) : EReal)) '' P.C) +
        (((1 - θ : ℝ) : EReal) * sSup ((fun c : Fin n → ℝ =>
          ((dotProduct c y : ℝ) : EReal)) '' P.C)) := by
  sorry

end «CAM-Bench-317»
