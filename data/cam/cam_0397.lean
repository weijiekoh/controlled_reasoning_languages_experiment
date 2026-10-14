import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-397»

def dualFunction {m : ℕ} (f0 : ℝ → ℝ) (fi : Fin m → ℝ → ℝ) :
    (Fin m → ℝ) → EReal :=
  fun lam =>
    sInf (Set.range fun x : ℝ =>
      (f0 x : EReal) + ∑ i : Fin m, (((lam i) * (fi i x)) : EReal))

def dualFeasible {m : ℕ} (lam : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, 0 ≤ lam i

def strictFeasibleSet {α : Type*} {m : ℕ} (fi : Fin m → α → ℝ) : Set α :=
  {x | ∀ i : Fin m, fi i x < 0}

def centeringObjective {α : Type*} {m : ℕ} (t : ℝ) (f0 : α → ℝ)
    (fi : Fin m → α → ℝ) (x : α) : EReal :=
  if ht : 0 < t then
    if hx : ∀ i : Fin m, fi i x < 0 then
      (t * f0 x : EReal) - ∑ i : Fin m, (Real.log (-fi i x) : EReal)
    else
      ⊤
  else
    ⊤

def logarithmicBarrier {m : ℕ} (fi : Fin m → ℝ → ℝ) : ℝ → EReal :=
  fun x =>
    if hx : ∀ i : Fin m, fi i x < 0 then
      -∑ i : Fin m, (Real.log (-fi i x) : EReal)
    else
      ⊤

structure ConvexInequalityConstrainedProblem (m : ℕ) where
  n : ℕ
  f0 : (Fin n → ℝ) → ℝ
  fi : Fin m → (Fin n → ℝ) → ℝ
  f0_convex : ConvexOn ℝ Set.univ f0
  fi_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (fi i)

def ConvexInequalityConstrainedProblem.isFeasible {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) (x : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin m, P.fi i x ≤ 0

def ConvexInequalityConstrainedProblem.feasibleSet {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : Set (Fin P.n → ℝ) :=
  {x | P.isFeasible x}

def ConvexInequalityConstrainedProblem.objective {m : ℕ}
    (P : ConvexInequalityConstrainedProblem m) : (Fin P.n → ℝ) → ℝ :=
  P.f0

structure LagrangeDualProblem (m : ℕ) where
  objective : (Fin m → ℝ) → EReal

def LagrangeDualProblem.feasibleSet {m : ℕ} (_P : LagrangeDualProblem m) :
    Set (Fin m → ℝ) :=
  {lam | dualFeasible lam}

theorem centeringObjective_bounded_below_on_strictFeasibleSet
    {m : ℕ} (P : ConvexInequalityConstrainedProblem m)
    (hlam : ∃ lam : Fin m → ℝ, dualFeasible lam ∧ ∀ i : Fin m, 0 < lam i) :
    ∀ t : ℝ, 0 < t →
      ∃ C : EReal, ∀ x ∈ strictFeasibleSet P.fi, C ≤ centeringObjective t P.f0 P.fi x := by
  sorry

end «CAM-Bench-397»
