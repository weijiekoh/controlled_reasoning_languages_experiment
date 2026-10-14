import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-326»

structure ConvexLogisticProgram where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  μ : ℝ
  μ_pos : 0 < μ

def ConvexLogisticProgram.rowDot (P : ConvexLogisticProgram) (i : Fin P.m) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.A i j * x j

def ConvexLogisticProgram.objective (P : ConvexLogisticProgram) (x : Fin P.n → ℝ) : ℝ :=
  (∑ j : Fin P.n, P.c j * x j) +
    (1 / P.μ) * ∑ i : Fin P.m, Real.log (1 + Real.exp (P.μ * (P.rowDot i x - P.b i)))

def ConvexLogisticProgram.optimalValue (P : ConvexLogisticProgram) : ℝ :=
  sInf (ConvexLogisticProgram.objective P '' Set.univ)

structure PrimalDualLinearProgram where
  m : ℕ
  n : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

def PrimalDualLinearProgram.primalFeasible (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.m, (∑ j : Fin P.n, P.A i j * x j) ≤ P.b i

def PrimalDualLinearProgram.primalObjective (P : PrimalDualLinearProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j : Fin P.n, P.c j * x j

def PrimalDualLinearProgram.dualFeasible (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) : Prop :=
  (∀ j : Fin P.n, (∑ i : Fin P.m, P.A i j * z i) + P.c j = 0) ∧
    ∀ i : Fin P.m, 0 ≤ z i

def PrimalDualLinearProgram.dualObjective (P : PrimalDualLinearProgram) (z : Fin P.m → ℝ) : ℝ :=
  -∑ i : Fin P.m, P.b i * z i

def PrimalDualLinearProgram.primalOptimalValue (P : PrimalDualLinearProgram) : ℝ :=
  sInf (P.primalObjective '' {x | P.primalFeasible x})

def PrimalDualLinearProgram.dualOptimalValue (P : PrimalDualLinearProgram) : ℝ :=
  sSup (P.dualObjective '' {z | P.dualFeasible z})

theorem primal_dual_linear_program_optimalValue_le_convexLogisticProgram_optimalValue_le
    (P : PrimalDualLinearProgram)
    (Q : ConvexLogisticProgram)
    (hm : Q.m = P.m)
    (hn : Q.n = P.n)
    (hA : ∀ i : Fin P.m, ∀ j : Fin P.n, Q.A (Fin.cast hm.symm i) (Fin.cast hn.symm j) = P.A i j)
    (hb : ∀ i : Fin P.m, Q.b (Fin.cast hm.symm i) = P.b i)
    (hc : ∀ j : Fin P.n, Q.c (Fin.cast hn.symm j) = P.c j)
    (pStar : ℝ)
    (hp_primal : P.primalOptimalValue = pStar)
    (hp_dual : P.dualOptimalValue = pStar)
    (hz_exists : ∃ zStar : Fin P.m → ℝ,
      (P.dualFeasible zStar ∧ P.dualObjective zStar = P.dualOptimalValue) ∧
      (∀ i : Fin P.m, zStar i ≤ 1)) :
    pStar ≤ Q.optimalValue ∧
      Q.optimalValue ≤ pStar + (P.m : ℝ) * Real.log 2 / Q.μ := by
  sorry

end «CAM-Bench-326»
