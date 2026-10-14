import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-733»

open Matrix

structure EqualityConstrainedLeastSquares where
  m : Type
  n : Type
  p : Type
  instFintypeM : Fintype m
  instDecidableEqM : DecidableEq m
  instFintypeN : Fintype n
  instDecidableEqN : DecidableEq n
  instFintypeP : Fintype p
  instDecidableEqP : DecidableEq p
  A : Matrix m n ℝ
  b : m → ℝ
  G : Matrix p n ℝ
  h : p → ℝ
  rank_A : Matrix.rank A = Fintype.card n
  rank_G : Matrix.rank G = Fintype.card p

attribute [instance] EqualityConstrainedLeastSquares.instFintypeM
attribute [instance] EqualityConstrainedLeastSquares.instDecidableEqM
attribute [instance] EqualityConstrainedLeastSquares.instFintypeN
attribute [instance] EqualityConstrainedLeastSquares.instDecidableEqN
attribute [instance] EqualityConstrainedLeastSquares.instFintypeP
attribute [instance] EqualityConstrainedLeastSquares.instDecidableEqP

def EqualityConstrainedLeastSquares.obj (P : EqualityConstrainedLeastSquares) (x : P.n → ℝ) : ℝ :=
  ‖P.A.mulVec x - P.b‖ ^ 2

def EqualityConstrainedLeastSquares.feasible (P : EqualityConstrainedLeastSquares) (x : P.n → ℝ) : Prop :=
  P.G.mulVec x = P.h

def EqualityConstrainedLeastSquares.Q (P : EqualityConstrainedLeastSquares) : Matrix P.n P.n ℝ :=
  P.A.transpose * P.A

def EqualityConstrainedLeastSquares.q (P : EqualityConstrainedLeastSquares) : P.n → ℝ :=
  P.A.transpose.mulVec P.b

theorem lagrangian_and_dual_function_formula
    (P : EqualityConstrainedLeastSquares) :
    ∃ L : (P.n → ℝ) → (P.p → ℝ) → ℝ,
      ∃ g : (P.p → ℝ) → ℝ,
        (∀ x lam, L x lam = P.obj x + 2 * dotProduct lam (P.G.mulVec x - P.h)) ∧
        (∀ lam, g lam = sInf (Set.range fun x : P.n → ℝ => L x lam)) := by
  sorry

end «CAM-Bench-733»
