import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-327»

structure QuadraticBallConstrainedProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ
  symmetric_A : A.IsSymm

def QuadraticBallConstrainedProblem.objective
    {n : ℕ} (P : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (P.A.mulVec x) + 2 * dotProduct P.b x

def QuadraticBallConstrainedProblem.feasible
    {n : ℕ} (_P : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) : Prop :=
  dotProduct x x ≤ 1

def QuadraticBallConstrainedProblem.isOptimal
    {n : ℕ} (P : QuadraticBallConstrainedProblem n) (xStar : Fin n → ℝ) : Prop :=
  P.feasible xStar ∧ ∀ x, P.feasible x → P.objective xStar ≤ P.objective x

def QuadraticBallConstrainedProblem.dualObjective
    {n : ℕ} (P : QuadraticBallConstrainedProblem n) (lam : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ x : Fin n → ℝ,
    v = P.objective x + lam * (dotProduct x x - 1)}

def QuadraticBallConstrainedProblem.strongDualityAt
    {n : ℕ} (P : QuadraticBallConstrainedProblem n) (xStar : Fin n → ℝ) (lamStar : ℝ) :
    Prop :=
  P.isOptimal xStar ∧
    0 ≤ lamStar ∧
    P.dualObjective lamStar = P.objective xStar ∧
    ∀ lam : ℝ, 0 ≤ lam → P.dualObjective lam ≤ P.dualObjective lamStar

theorem quadratic_ball_kkt_implies_strong_duality_and_global_optimal
    {n : ℕ} (P : QuadraticBallConstrainedProblem n) (x : Fin n → ℝ) (lam : ℝ)
    (hx_feas : P.feasible x)
    (hlam_nonneg : 0 ≤ lam)
    (hpsd : ∀ z : Fin n → ℝ,
      0 ≤ dotProduct z (((P.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec z)))
    (hstationary :
      ((P.A + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x) = fun i => -P.b i)
    (hcomp : lam * (1 - dotProduct x x) = 0) :
    P.strongDualityAt x lam ∧ P.isOptimal x := by
  sorry

end «CAM-Bench-327»
