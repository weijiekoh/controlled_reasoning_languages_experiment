import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-17»

def Lagrangian {E ι : Type*} [Fintype ι] (f : E → ℝ) (c : ι → E → ℝ) (x : E) (lam : ι → ℝ) : ℝ :=
  f x - ∑ i, lam i * c i x

def KKTConditions
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (gradL : E → (ι → ℝ) → E → Prop)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  gradient (fun y => Lagrangian f c y lam) x = 0 ∧
  (∀ i ∈ Eeq, c i x = 0) ∧
  (∀ i ∈ Ineq, c i x ≥ 0) ∧
  (∀ i ∈ Ineq, lam i ≥ 0) ∧
  ∀ i ∈ Ineq, lam i * c i x = 0

def LICQ
    {E ι : Type*}
    [AddCommMonoid E]
    [Module ℝ E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (cgrad : ι → E → E)
    (c : ι → E → ℝ)
    (x : E) : Prop :=
  LinearIndependent ℝ (fun i : {i // i ∈ Eeq ∪ {j | j ∈ Ineq ∧ c j x = 0}} => cgrad i.1 x)

def activeSet
    {E ι : Type*}
    (Ineq : Set ι)
    (c : ι → E → ℝ)
    (x : E) : Set ι :=
  {i | i ∈ Ineq ∧ c i x = 0}

def Stationarity
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (gradL : E → (ι → ℝ) → E → Prop)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  gradient (fun y => Lagrangian f c y lam) x = 0

def PrimalFeasible
    {E ι : Type*}
    (Eeq Ineq : Set ι)
    (c : ι → E → ℝ)
    (x : E) : Prop :=
  (∀ i ∈ Eeq, c i x = 0) ∧
  (∀ i ∈ Ineq, c i x ≥ 0)

def DualFeasible
    {ι : Type*}
    (Ineq : Set ι)
    (lam : ι → ℝ) : Prop :=
  ∀ i ∈ Ineq, lam i ≥ 0

def ComplementarySlackness
    {E ι : Type*}
    (Ineq : Set ι)
    (c : ι → E → ℝ)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  ∀ i ∈ Ineq, lam i * c i x = 0

def MultiplierVector
    {E ι : Type*}
    [OfNat E 0]
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (gradL : E → (ι → ℝ) → E → Prop)
    (x : E)
    (lam : ι → ℝ) : Prop :=
  Stationarity f c gradL x lam ∧
  PrimalFeasible Eeq Ineq c x ∧
  DualFeasible Ineq lam ∧
  ComplementarySlackness Ineq c x lam

theorem kkt_multiplier_unique_under_LICQ
    {E ι : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    [Fintype ι]
    (Eeq Ineq : Set ι)
    (f : E → ℝ)
    (c : ι → E → ℝ)
    (gradL : E → (ι → ℝ) → E → Prop)
    (x : E)
    (lamStar : ι → ℝ)
    (hKKTStar : MultiplierVector Eeq Ineq f c gradL x lamStar)
    (hLICQ : LICQ Eeq Ineq (fun i y => gradient (c i) y) c x)
    : ∀ lam : ι → ℝ,
        MultiplierVector Eeq Ineq f c gradL x lam →
        lam = lamStar := by
  sorry

end «CAM-Bench-17»
