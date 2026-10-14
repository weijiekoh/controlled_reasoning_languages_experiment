import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-585»

structure L1FitWithInfinityNormBound
    (m n : Type)
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n] where
  A : Matrix m n ℝ
  b : m → ℝ

def L1FitWithInfinityNormBound.isFeasible
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitWithInfinityNormBound m n) (x : n → ℝ) : Prop :=
  ∀ j, |x j| ≤ 1

def L1FitWithInfinityNormBound.objective
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitWithInfinityNormBound m n) (x : n → ℝ) : ℝ :=
  ∑ i, |p.A.mulVec x i - p.b i|

def L1FitWithInfinityNormBound.isOptimal
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitWithInfinityNormBound m n) (x : n → ℝ) : Prop :=
  p.isFeasible x ∧
    ∀ y : n → ℝ, p.isFeasible y → p.objective x ≤ p.objective y

structure L1FitInfinityBoundLinearProgram
    (m n : Type)
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n] where
  base : L1FitWithInfinityNormBound m n

def L1FitInfinityBoundLinearProgram.isFeasible
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitInfinityBoundLinearProgram m n) (x : n → ℝ) (y : m → ℝ) : Prop :=
  (∀ i, -(y i) ≤ p.base.A.mulVec x i - p.base.b i) ∧
    (∀ i, p.base.A.mulVec x i - p.base.b i ≤ y i) ∧
    (∀ j, -(1 : ℝ) ≤ x j) ∧
    ∀ j, x j ≤ 1

def L1FitInfinityBoundLinearProgram.objective
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitInfinityBoundLinearProgram m n) (y : m → ℝ) : ℝ :=
  ∑ i, y i

def L1FitInfinityBoundLinearProgram.isOptimal
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitInfinityBoundLinearProgram m n) (x : n → ℝ) (y : m → ℝ) : Prop :=
  p.isFeasible x y ∧
    ∀ x' : n → ℝ, ∀ y' : m → ℝ,
      p.isFeasible x' y' → p.objective y ≤ p.objective y'

theorem l1FitInfinityBoundLinearProgram_equivalence
    {m n : Type}
    [Fintype m]
    [Fintype n]
    [DecidableEq m]
    [DecidableEq n]
    (p : L1FitInfinityBoundLinearProgram m n) :
    (∀ x : n → ℝ, p.base.isOptimal x ↔ ∃ y : m → ℝ, p.isOptimal x y) ∧
      (∀ v : ℝ,
        (∃ x : n → ℝ, p.base.isOptimal x ∧ p.base.objective x = v) ↔
          ∃ x : n → ℝ, ∃ y : m → ℝ, p.isOptimal x y ∧ p.objective y = v) := by
  sorry

end «CAM-Bench-585»
