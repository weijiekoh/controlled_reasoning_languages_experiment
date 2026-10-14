import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-304»

open scoped BigOperators

def dualFunction {n m : ℕ} (h₀ : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun μ =>
    sInf {r : EReal | ∃ x : Fin n → ℝ, r = ((h₀ x + ∑ i, μ i * f i x : ℝ) : EReal)}

def DualFeasible {m : ℕ} (μ : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ μ i

structure ConvexInequalityConstrainedProblem (n m : ℕ) where
  h₀ : (Fin n → ℝ) → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ

def ConvexInequalityConstrainedProblem.IsFeasible {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m) (x : Fin n → ℝ) : Prop :=
  ∀ i, P.f i x ≤ 0

def ConvexInequalityConstrainedProblem.objective {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m) (x : Fin n → ℝ) : ℝ :=
  P.h₀ x

def ConvexInequalityConstrainedProblem.dualFunction {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m) : (Fin m → ℝ) → EReal :=
  fun _ => 0

def ConvexInequalityConstrainedProblem.DualFeasible {n m : ℕ}
    (P : ConvexInequalityConstrainedProblem n m) (μ : Fin m → ℝ) : Prop :=
  ∀ i, 0 ≤ μ i

structure ExponentialObjectiveConvexProblem (n m : ℕ) where
  f₀ : (Fin n → ℝ) → ℝ
  f : Fin m → (Fin n → ℝ) → ℝ
  f₀_convex : ConvexOn ℝ Set.univ f₀
  f_convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  f₀_differentiable : Differentiable ℝ f₀
  f_differentiable : ∀ i, Differentiable ℝ (f i)

def ExponentialObjectiveConvexProblem.baseProblem {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) : ConvexInequalityConstrainedProblem n m :=
  { h₀ := P.f₀
    f := P.f }

def ExponentialObjectiveConvexProblem.exponentialObjective {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) : (Fin n → ℝ) → ℝ :=
  fun x => Real.exp (P.f₀ x)

def ExponentialObjectiveConvexProblem.exponentialProblem {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) : ConvexInequalityConstrainedProblem n m :=
  { h₀ := P.exponentialObjective
    f := P.f }

def ExponentialObjectiveConvexProblem.IsFeasible {n m : ℕ}
    (P : ExponentialObjectiveConvexProblem n m) (x : Fin n → ℝ) : Prop :=
  P.baseProblem.IsFeasible x

theorem exp_reweighted_lagrangian_minimizer
    {n m : ℕ} (P : ExponentialObjectiveConvexProblem n m) (lam : Fin m → ℝ) (xbar : Fin n → ℝ)
    (hlam : P.baseProblem.DualFeasible lam)
    (hmin :
      ∀ x : Fin n → ℝ,
        P.f₀ xbar + ∑ i, lam i * P.f i xbar ≤ P.f₀ x + ∑ i, lam i * P.f i x)
    : ∃ lam_tilde : Fin m → ℝ,
        P.exponentialProblem.DualFeasible lam_tilde ∧
          ∀ x : Fin n → ℝ,
            Real.exp (P.f₀ xbar) + ∑ i, lam_tilde i * P.f i xbar ≤
              Real.exp (P.f₀ x) + ∑ i, lam_tilde i * P.f i x := by
  sorry

end «CAM-Bench-304»
