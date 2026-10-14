import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-357»

structure SecondOrderConeProgram where
  n : ℕ
  m : ℕ
  objectiveLinear : Fin n → ℝ
  objectiveConstant : ℝ
  eqCount : ℕ
  eqMatrix : Fin eqCount → Fin n → ℝ
  eqRhs : Fin eqCount → ℝ
  coneCount : ℕ
  coneDim : Fin coneCount → ℕ
  coneMatrix : (i : Fin coneCount) → Fin (coneDim i) → Fin n → ℝ
  coneOffset : (i : Fin coneCount) → Fin (coneDim i) → ℝ
  coneAffine : Fin coneCount → Fin n → ℝ
  coneScalar : Fin coneCount → ℝ

def SecondOrderConeProgram.objective (p : SecondOrderConeProgram) (z : Fin p.n → ℝ) : ℝ :=
  ∑ j : Fin p.n, p.objectiveLinear j * z j + p.objectiveConstant

def SecondOrderConeProgram.satisfiesEqualities (p : SecondOrderConeProgram) (z : Fin p.n → ℝ) : Prop :=
  ∀ i : Fin p.eqCount, ∑ j : Fin p.n, p.eqMatrix i j * z j = p.eqRhs i

def SecondOrderConeProgram.satisfiesConeConstraint (p : SecondOrderConeProgram) (i : Fin p.coneCount)
    (z : Fin p.n → ℝ) : Prop :=
  ‖fun k : Fin (p.coneDim i) => ∑ j : Fin p.n, p.coneMatrix i k j * z j + p.coneOffset i k‖
    ≤ (∑ j : Fin p.n, p.coneAffine i j * z j) + p.coneScalar i

def SecondOrderConeProgram.IsFeasible (p : SecondOrderConeProgram) (z : Fin p.n → ℝ) : Prop :=
  p.satisfiesEqualities z ∧ ∀ i : Fin p.coneCount, p.satisfiesConeConstraint i z

structure DistanceToConvexHullProblem where
  n : ℕ
  m : ℕ
  a : Fin n → ℝ
  sets : Fin m → Set (Fin n → ℝ)

def DistanceToConvexHullProblem.feasibleSet (p : DistanceToConvexHullProblem) : Set (Fin p.n → ℝ) :=
  convexHull ℝ (⋃ i : Fin p.m, p.sets i)

def DistanceToConvexHullProblem.objective (p : DistanceToConvexHullProblem) (x : Fin p.n → ℝ) : ℝ :=
  ‖x - p.a‖

def DistanceToConvexHullProblem.IsFeasible (p : DistanceToConvexHullProblem) (x : Fin p.n → ℝ) : Prop :=
  x ∈ p.feasibleSet

structure ConvexHullSOCP where
  n : ℕ
  m : ℕ
  a : Fin n → ℝ
  A : Fin m → Fin n → Fin n → ℝ
  b : Fin m → Fin n → ℝ

def ConvexHullSOCP.xExpr (p : ConvexHullSOCP) (y : (i : Fin p.m) → Fin p.n → ℝ)
    (lam : Fin p.m → ℝ) : Fin p.n → ℝ :=
  fun j =>
    ∑ i : Fin p.m, ((∑ k : Fin p.n, p.A i j k * y i k) + lam i * p.b i j)

def ConvexHullSOCP.objective (_p : ConvexHullSOCP) (t : ℝ) : ℝ := t

def ConvexHullSOCP.IsFeasible (p : ConvexHullSOCP) (x : Fin p.n → ℝ) (t : ℝ)
    (y : (i : Fin p.m) → Fin p.n → ℝ) (lam : Fin p.m → ℝ) : Prop :=
  ‖x - p.a‖ ≤ t ∧
  x = p.xExpr y lam ∧
  (∀ i : Fin p.m, ‖y i‖ ≤ lam i) ∧
  (∀ i : Fin p.m, 0 ≤ lam i) ∧
  (∑ i : Fin p.m, lam i) = 1

theorem distanceToConvexHull_equivalent_to_convexHullSOCP
    (n m : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (a : Fin n → ℝ)
    (A : Fin m → Fin n → Fin n → ℝ)
    (b : Fin m → Fin n → ℝ) :
    let distProblem : DistanceToConvexHullProblem :=
      { n := n
        m := m
        a := a
        sets := fun i =>
          {x | ∃ u : Fin n → ℝ, ‖u‖ ≤ (1 : ℝ) ∧ x = fun j => (∑ k : Fin n, A i j k * u k) + b i j} }
    let socp : ConvexHullSOCP :=
      { n := n
        m := m
        a := a
        A := A
        b := b }
    sInf {r : ℝ | ∃ x : Fin n → ℝ,
      distProblem.IsFeasible x ∧ distProblem.objective x = r} =
    sInf {r : ℝ | ∃ x : Fin n → ℝ, ∃ t : ℝ,
      ∃ y : (i : Fin m) → Fin n → ℝ, ∃ lam : Fin m → ℝ,
        socp.IsFeasible x t y lam ∧ socp.objective t = r} := by
  sorry

end «CAM-Bench-357»
