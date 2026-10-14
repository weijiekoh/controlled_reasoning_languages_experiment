import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-752»

structure LinfNormApproximationProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LinfNormApproximationProblem.objective {m n : ℕ}
    (p : LinfNormApproximationProblem m n) (x : Fin n → ℝ) : ℝ :=
  sInf {r : ℝ | ∀ i : Fin m, |p.A.mulVec x i - p.b i| ≤ r}

def LinfNormApproximationProblem.isMinimizer {m n : ℕ}
    (p : LinfNormApproximationProblem m n) (x : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, p.objective x ≤ p.objective y

theorem linfNormApproximationProblem_dual_form
    {m n : ℕ} (p : LinfNormApproximationProblem m n) :
    ∃ yStar : Fin m → ℝ,
      Matrix.mulVec p.Aᵀ yStar = 0 ∧
      (∑ i : Fin m, |yStar i|) ≤ (1 : ℝ) ∧
      ∀ y : Fin m → ℝ,
        Matrix.mulVec p.Aᵀ y = 0 →
        (∑ i : Fin m, |y i|) ≤ (1 : ℝ) →
        (-∑ i : Fin m, p.b i * y i) ≤ (-∑ i : Fin m, p.b i * yStar i) := by
  sorry

end «CAM-Bench-752»
