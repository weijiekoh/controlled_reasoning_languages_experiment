import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-604»

def euclideanLength {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

structure MatrixFractionalMinimizationProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  B : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  x : Fin n → ℝ
  nonneg : 0 ≤ x

def MatrixFractionalMinimizationProblem.systemMatrix
    {m n : ℕ} (p : MatrixFractionalMinimizationProblem m n) :
    Matrix (Fin m) (Fin m) ℝ :=
  1 + p.B * Matrix.diagonal p.x * p.B.transpose

def MatrixFractionalMinimizationProblem.residual
    {m n : ℕ} (p : MatrixFractionalMinimizationProblem m n) :
    Fin m → ℝ :=
  p.A.mulVec p.x + p.b

def MatrixFractionalMinimizationProblem.objective
    {m n : ℕ} (p : MatrixFractionalMinimizationProblem m n) :
    ℝ :=
  dotProduct (p.residual) (((p.systemMatrix)⁻¹).mulVec (p.residual))

structure MatrixFractionalSecondOrderConeProgram (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  B : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  t : ℝ
  s : Fin n → ℝ
  w : Fin n → ℝ
  x : Fin n → ℝ
  v : Fin m → ℝ
  balance : v + B.mulVec w = A.mulVec x + b
  cone_vt :
    euclideanLength (fun j : Fin 2 => if j.1 = 0 then 2 * euclideanLength v else t - 1) ≤
      t + 1
  cone_wsx :
    ∀ i : Fin n,
      euclideanLength (fun j : Fin 2 => if j.1 = 0 then 2 * w i else s i - x i) ≤
        s i + x i
  nonneg : 0 ≤ x

def MatrixFractionalSecondOrderConeProgram.objective
    {m n : ℕ} (p : MatrixFractionalSecondOrderConeProgram m n) : ℝ :=
  p.t + ∑ i : Fin n, p.s i

def socPair (a b : ℝ) : Fin 2 → ℝ :=
  fun j => if j.1 = 0 then a else b

theorem matrix_fractional_minimization_equiv_second_order_cone_program
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    {r : ℝ |
      ∃ p : MatrixFractionalMinimizationProblem m n,
        p.A = A ∧ p.B = B ∧ p.b = b ∧ p.objective = r} =
    {r : ℝ |
      ∃ q : MatrixFractionalSecondOrderConeProgram m n,
        q.A = A ∧ q.B = B ∧ q.b = b ∧ q.objective = r} := by
  sorry

end «CAM-Bench-604»
