import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-588»

structure RobustLinearProgram (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] where
  uncertaintySet : Set (Matrix m n ℝ)
  b : m → ℝ
  c : n → ℝ

def RobustLinearProgram.isFeasible
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : RobustLinearProgram m n) (x : n → ℝ) : Prop :=
  ∀ A ∈ p.uncertaintySet, A.mulVec x ≤ p.b

def RobustLinearProgram.objectiveValue
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : RobustLinearProgram m n) (x : n → ℝ) : ℝ :=
  dotProduct p.c x

structure ReformulatedLinearProgram
    (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] where
  Abar : Matrix m n ℝ
  V : Matrix m n ℝ
  b : m → ℝ
  c : n → ℝ

def ReformulatedLinearProgram.isFeasible
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ReformulatedLinearProgram m n) (x y : n → ℝ) : Prop :=
  p.Abar.mulVec x + p.V.mulVec y ≤ p.b ∧ (-y ≤ x ∧ x ≤ y)

def ReformulatedLinearProgram.objectiveValue
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ReformulatedLinearProgram m n) (x _y : n → ℝ) : ℝ :=
  dotProduct p.c x

theorem robust_linear_program_equivalent_to_reformulation
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Abar V : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hV : ∀ i j, 0 ≤ V i j) :
    let robust : RobustLinearProgram m n :=
      { uncertaintySet := {A | ∀ i j, Abar i j - V i j ≤ A i j ∧ A i j ≤ Abar i j + V i j}
        b := b
        c := c }
    let reform : ReformulatedLinearProgram m n :=
      { Abar := Abar
        V := V
        b := b
        c := c }
    ∀ x : n → ℝ, robust.isFeasible x ↔ ∃ y : n → ℝ, reform.isFeasible x y := by
  sorry

end «CAM-Bench-588»
