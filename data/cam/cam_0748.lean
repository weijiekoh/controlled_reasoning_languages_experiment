import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-748»

structure SimplexLinearProgram (n : ℕ) where
  c : Fin n → ℝ

def SimplexLinearProgram.feasibleSet {n : ℕ} (_P : SimplexLinearProgram n) :
    Set (Fin n → ℝ) :=
  {x | (∑ i, x i) = 1 ∧ ∀ i, 0 ≤ x i}

def SimplexLinearProgram.objective {n : ℕ}
    (P : SimplexLinearProgram n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, P.c i * x i

def SimplexLinearProgram.standardBasisVector {n : ℕ} (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i then 1 else 0

theorem simplex_linear_program_optimal_at_standardBasisVector_of_min_coeff
    {n : ℕ} [NeZero n] (P : SimplexLinearProgram n) :
    ∃ i : Fin n,
      IsMinOn P.objective (P.feasibleSet) (SimplexLinearProgram.standardBasisVector i) ∧
      P.objective (SimplexLinearProgram.standardBasisVector i) = iInf fun j : Fin n => P.c j := by
  sorry

end «CAM-Bench-748»
