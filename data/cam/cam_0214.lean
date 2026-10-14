import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-214»

def IsGroundStateEigenvector {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (v : n → ℝ) : Prop :=
  v ≠ 0 ∧ Matrix.IsSymm H ∧ ∃ μ : ℝ, H.mulVec v = μ • v

def EnergyGap {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (v : n → ℝ) (μ : ℝ) : ℝ :=
  sSup {t : ℝ |
    (H - μ • (1 : Matrix n n ℝ) -
      t • ((1 : Matrix n n ℝ) - Matrix.vecMulVec v v)).PosSemidef}

def IsQuasiconvexOptimizationProblem {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ) (feasibleSet : Set E) : Prop :=
  Convex ℝ feasibleSet ∧ QuasiconvexOn ℝ feasibleSet f

structure EnergyGapQuasiconvexProblem (k : ℕ) where
  H : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ
  x : Fin k → ℝ
  μ : ℝ
  t : ℝ
  v : Fin k → ℝ

def EnergyGapQuasiconvexProblem.isFeasible {k : ℕ} (P : EnergyGapQuasiconvexProblem k) : Prop :=
  Matrix.IsSymm (P.H P.x) ∧
    IsGroundStateEigenvector (P.H P.x) P.v ∧
    (P.H P.x).mulVec P.v = P.μ • P.v ∧
    (∀ i : Fin k, |P.x i| ≤ 1) ∧
    (P.H P.x - P.μ • (1 : Matrix (Fin k) (Fin k) ℝ) -
        P.t • ((1 : Matrix (Fin k) (Fin k) ℝ) - Matrix.vecMulVec P.v P.v)).PosSemidef

def EnergyGapQuasiconvexProblem.objective {k : ℕ} (P : EnergyGapQuasiconvexProblem k) : ℝ :=
  P.t

theorem energyGapQuasiconvexProblem_feasible_certifies_gap
    {k : ℕ}
    (P : EnergyGapQuasiconvexProblem k)
    (hgap_bdd : BddAbove {τ : ℝ |
      (P.H P.x - P.μ • (1 : Matrix (Fin k) (Fin k) ℝ) -
        τ • ((1 : Matrix (Fin k) (Fin k) ℝ) - Matrix.vecMulVec P.v P.v)).PosSemidef}) :
    P.isFeasible →
      P.t ∈ {τ : ℝ |
        (P.H P.x - P.μ • (1 : Matrix (Fin k) (Fin k) ℝ) -
          τ • ((1 : Matrix (Fin k) (Fin k) ℝ) - Matrix.vecMulVec P.v P.v)).PosSemidef} ∧
      P.t ≤ EnergyGap (P.H P.x) P.v P.μ := by
  sorry

end «CAM-Bench-214»
