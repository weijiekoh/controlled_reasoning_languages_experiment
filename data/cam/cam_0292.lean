import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-292»

structure LambdaThresholdConvexProgram where
  n : ℕ
  m : ℕ
  k : ℕ
  f0 : (Fin n → ℝ) → ℝ
  fi : Fin m → (Fin n → ℝ) → ℝ

def LambdaThresholdConvexProgram.objectiveFn
    (P : LambdaThresholdConvexProgram) (x : Fin P.n → ℝ) (_lam : ℝ) : ℝ :=
  P.f0 x

def LambdaThresholdConvexProgram.feasible
    (P : LambdaThresholdConvexProgram) (x : Fin P.n → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧
    (∑ i : Fin P.m, max (0 : ℝ) (1 + lam * P.fi i x)) ≤ P.m - P.k

def LambdaThresholdConvexProgram.isFeasible
    (P : LambdaThresholdConvexProgram) (x : Fin P.n → ℝ) (lam : ℝ) : Prop :=
  P.feasible x lam

def LambdaThresholdConvexProgram.objective
    (P : LambdaThresholdConvexProgram) (x : Fin P.n → ℝ) (_lam : ℝ) : ℝ :=
  P.f0 x

theorem lambdaThresholdConvexProgram_changeOfVariables_equiv
    (P : LambdaThresholdConvexProgram)
    (hk₁ : 1 ≤ P.k)
    (hk₂ : P.k ≤ P.m) :
    ∀ x : Fin P.n → ℝ, ∀ lam t : ℝ, 0 < lam → t = 1 / lam →
      (LambdaThresholdConvexProgram.isFeasible P x lam ↔
        0 < t ∧
          (∑ i : Fin P.m, max (0 : ℝ) (t + P.fi i x)) ≤ (P.m - P.k : ℕ) * t) := by
  sorry

end «CAM-Bench-292»
