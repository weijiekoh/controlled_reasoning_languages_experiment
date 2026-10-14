import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-408»

def LogarithmicBarrier {E : Type*} {I : Type*} [Fintype I] (f : I → E → ℝ) (x : E) : EReal :=
  if ∀ i : I, f i x < 0 then
    ↑(-∑ i : I, Real.log (-(f i x)))
  else
    ⊤

structure ConvexOptimizationProblem where
  n : ℕ
  p : ℕ
  m : Type
  instFintypeM : Fintype m
  objective : (Fin n → ℝ) → ℝ
  constraint : m → (Fin n → ℝ) → ℝ
  A : (Fin n → ℝ) → (Fin p → ℝ)
  b : Fin p → ℝ

attribute [instance] ConvexOptimizationProblem.instFintypeM

def ConvexOptimizationProblem.isFeasible (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  P.A x = P.b ∧ ∀ i : P.m, P.constraint i x ≤ 0

def ConvexOptimizationProblem.isStrictlyFeasible (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : Prop :=
  P.A x = P.b ∧ ∀ i : P.m, P.constraint i x < 0

def ConvexOptimizationProblem.barrier (P : ConvexOptimizationProblem) (x : Fin P.n → ℝ) : EReal :=
  LogarithmicBarrier P.constraint x

def ConvexOptimizationProblem.centralPathPoint (P : ConvexOptimizationProblem)
    (t : ℝ) (x : Fin P.n → ℝ) : Prop :=
  0 < t ∧
    P.A x = P.b ∧
    ∀ y : Fin P.n → ℝ,
      P.A y = P.b →
        t * P.objective x + P.barrier x ≤ t * P.objective y + P.barrier y

def ConvexOptimizationProblem.centralPath (P : ConvexOptimizationProblem) : ℝ → Set (Fin P.n → ℝ) :=
  fun t => {x : Fin P.n → ℝ | P.centralPathPoint t x}

def LogarithmicBarrierSubproblem.objective (P : ConvexOptimizationProblem) (t : ℝ)
    (x : Fin P.n → ℝ) : EReal :=
  (t : EReal) * (P.objective x : EReal) + P.barrier x

def LogarithmicBarrierSubproblem.isFeasible (P : ConvexOptimizationProblem) (_t : ℝ)
    (x : Fin P.n → ℝ) : Prop :=
  P.A x = P.b

def LogarithmicBarrierSubproblem.isSolution (P : ConvexOptimizationProblem) (t : ℝ)
    (x : Fin P.n → ℝ) : Prop :=
  0 < t ∧
    LogarithmicBarrierSubproblem.isFeasible P t x ∧
    ∀ y : Fin P.n → ℝ,
      LogarithmicBarrierSubproblem.isFeasible P t y →
        LogarithmicBarrierSubproblem.objective P t x ≤
          LogarithmicBarrierSubproblem.objective P t y

def LogarithmicBarrierSubproblem.solutionSet (P : ConvexOptimizationProblem) (t : ℝ) :
    Set (Fin P.n → ℝ) :=
  {x : Fin P.n → ℝ | LogarithmicBarrierSubproblem.isSolution P t x}

def ShiftedBarrierProblem.objective (P : ConvexOptimizationProblem) (u : ℝ)
    (x : Fin P.n → ℝ) : EReal :=
  if P.objective x < u then
    ↑(-Real.log (u - P.objective x)) + P.barrier x
  else
    ⊤

def ShiftedBarrierProblem.isFeasible (P : ConvexOptimizationProblem) (_u : ℝ)
    (x : Fin P.n → ℝ) : Prop :=
  P.A x = P.b

def ShiftedBarrierProblem.isSolution (P : ConvexOptimizationProblem) (u : ℝ)
    (x : Fin P.n → ℝ) : Prop :=
  P.objective x < u ∧
    ShiftedBarrierProblem.isFeasible P u x ∧
    ∀ y : Fin P.n → ℝ,
      ShiftedBarrierProblem.isFeasible P u y →
        ShiftedBarrierProblem.objective P u x ≤
          ShiftedBarrierProblem.objective P u y

def ShiftedBarrierProblem (P : ConvexOptimizationProblem) (u : ℝ) :
    Set (Fin P.n → ℝ) :=
  {x : Fin P.n → ℝ | ShiftedBarrierProblem.isSolution P u x}

def LogarithmicBarrierSubproblem.realObjective (P : ConvexOptimizationProblem) (t : ℝ)
    (x : Fin P.n → ℝ) : ℝ :=
  t * P.objective x - ∑ i : P.m, Real.log (-(P.constraint i x))

def ShiftedBarrierProblem.realObjective (P : ConvexOptimizationProblem) (u : ℝ)
    (x : Fin P.n → ℝ) : ℝ :=
  -Real.log (u - P.objective x) - ∑ i : P.m, Real.log (-(P.constraint i x))

def IsStationary {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  fderiv ℝ F x = 0

theorem shiftedBarrier_stationary_iff_centralPath_stationary
    (P : ConvexOptimizationProblem)
    (u : ℝ)
    (x : Fin P.n → ℝ)
    (_hstrict : P.isStrictlyFeasible x)
    (_hux : P.objective x < u) :
    IsStationary (ShiftedBarrierProblem.realObjective P u) x ↔
      IsStationary
        (LogarithmicBarrierSubproblem.realObjective P ((u - P.objective x)⁻¹)) x := by
  sorry

end «CAM-Bench-408»
