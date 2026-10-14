import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-598»

structure QuarticResidualMinimization (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def QuarticResidualMinimization.residual {m n : ℕ} (p : QuarticResidualMinimization m n)
    (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  (∑ j : Fin n, p.A i j * x j) - p.b i

def QuarticResidualMinimization.objective {m n : ℕ} (p : QuarticResidualMinimization m n)
    (x : Fin n → ℝ) : ℝ :=
  Real.rpow (∑ i : Fin m, (p.residual i x) ^ 4) (1 / 4 : ℝ)

def QuarticResidualMinimization.IsMinimizer {m n : ℕ} (p : QuarticResidualMinimization m n)
    (xStar : Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, p.objective xStar ≤ p.objective x

structure QuarticResidualQCQP (m n : ℕ) where
  base : QuarticResidualMinimization m n

def QuarticResidualQCQP.objective {m n : ℕ} (p : QuarticResidualQCQP m n)
    (z : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, (z i) ^ 2

def QuarticResidualQCQP.is_feasible {m n : ℕ} (p : QuarticResidualQCQP m n)
    (x : Fin n → ℝ) (y z : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, p.base.residual i x = y i) ∧
  ∀ i : Fin m, (y i) ^ 2 ≤ z i

def QuarticResidualQCQP.IsMinimizer {m n : ℕ} (p : QuarticResidualQCQP m n)
    (xStar : Fin n → ℝ) (yStar zStar : Fin m → ℝ) : Prop :=
  p.is_feasible xStar yStar zStar ∧
    ∀ x : Fin n → ℝ, ∀ y z : Fin m → ℝ,
      p.is_feasible x y z → p.objective zStar ≤ p.objective z

theorem quarticResidualMinimizer_iff_qcqp_exists
    {m n : ℕ} (p : QuarticResidualMinimization m n) (xStar : Fin n → ℝ) :
    p.IsMinimizer xStar ↔
      ∃ yStar zStar : Fin m → ℝ,
        (QuarticResidualQCQP.mk p).IsMinimizer xStar yStar zStar := by
  sorry

end «CAM-Bench-598»
