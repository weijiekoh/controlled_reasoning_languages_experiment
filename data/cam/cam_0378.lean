import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-378»

def logDet {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℝ) : ℝ :=
  Real.log (Matrix.det X)

structure LogDetSemidefiniteProgram (n : Type*) [Fintype n] [DecidableEq n] where
  C : Matrix n n ℝ
  C_symm : C.IsSymm

def LogDetSemidefiniteProgram.isFeasible {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) : Prop :=
  X.IsSymm ∧
  X.PosDef ∧
  X.diag = fun _ => (1 : ℝ)

def LogDetSemidefiniteProgram.objective {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) : ℝ :=
  Matrix.trace (P.C * X) - logDet X

theorem logDetSemidefiniteProgram_optimality_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : LogDetSemidefiniteProgram n) (X : Matrix n n ℝ) :
    IsMinOn (fun Y : Matrix n n ℝ => P.objective Y)
      {Y | Y.IsSymm ∧ Y.PosDef ∧ Y.diag = fun _ => (1 : ℝ)} X ↔
      X.IsSymm ∧
      X.PosDef ∧
      (∃ d : n → ℝ, X⁻¹ - P.C = Matrix.diagonal d) ∧
      X.diag = fun _ => (1 : ℝ) := by
  sorry

end «CAM-Bench-378»
