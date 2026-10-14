import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-729»

def IsMoorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop :=
  (A * B * A = A ∧
  B * A * B = B ∧
  (A * B)ᵀ = A * B ∧
  (B * A)ᵀ = B * A) ∧
  ∀ C : Matrix n m ℝ,
    (A * C * A = A ∧
    C * A * C = C ∧
    (A * C)ᵀ = A * C ∧
    (C * A)ᵀ = C * A) → C = B

def moorePenrosePseudoinverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : Set (Matrix n m ℝ) :=
  {B | IsMoorePenrosePseudoinverse A B}

structure UnconstrainedQuadraticProgram (n : Type*) [Fintype n] where
  A : Matrix n n ℝ
  b : n → ℝ
  symm_A : Aᵀ = A

def UnconstrainedQuadraticProgram.objective {n : Type*} [Fintype n]
    (p : UnconstrainedQuadraticProgram n) (x : n → ℝ) : ℝ :=
  dotProduct x (p.A.mulVec x) + 2 * dotProduct p.b x

def UnconstrainedQuadraticProgram.isMinimizer {n : Type*} [Fintype n]
    (p : UnconstrainedQuadraticProgram n) (x : n → ℝ) : Prop :=
  ∀ y : n → ℝ, p.objective x ≤ p.objective y

theorem unconstrainedQuadraticProgram_has_optimal_solution_iff
    {n : Type*} [Fintype n] [DecidableEq n] (p : UnconstrainedQuadraticProgram n) :
    (((∃ x : n → ℝ, p.isMinimizer x) ↔
      ((∀ x : n → ℝ, 0 ≤ dotProduct x (p.A.mulVec x)) ∧
        (∀ z : n → ℝ, p.A.mulVec z = 0 → dotProduct p.b z = 0))) ∧
    (((∀ x : n → ℝ, 0 ≤ dotProduct x (p.A.mulVec x)) ∧
        (∀ z : n → ℝ, p.A.mulVec z = 0 → dotProduct p.b z = 0)) →
      ∀ Adag : Matrix n n ℝ, IsMoorePenrosePseudoinverse p.A Adag →
        ({x : n → ℝ | p.isMinimizer x} =
          {x : n → ℝ | p.A.mulVec x = fun i => -p.b i}) ∧
        ({x : n → ℝ | p.isMinimizer x} =
          {x : n → ℝ | ∃ z : n → ℝ,
              x = fun i => -(Adag.mulVec p.b) i + (z i - (Adag.mulVec (p.A.mulVec z)) i)}) ∧
        (∀ x : n → ℝ, p.isMinimizer x →
          p.objective x = -dotProduct p.b (Adag.mulVec p.b)))) := by
  sorry

end «CAM-Bench-729»
