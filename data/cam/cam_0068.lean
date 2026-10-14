import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-68»

def HasFullRowRank {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : Prop :=
  Matrix.rank A = Fintype.card m

structure EqualityConstrainedQuadraticProgram
    (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  G : Matrix n n ℝ
  A : Matrix m n ℝ
  c : n → ℝ
  b : m → ℝ

def EqualityConstrainedQuadraticProgram.isFeasible
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram m n) (x : n → ℝ) : Prop :=
  P.A.mulVec x = P.b

def EqualityConstrainedQuadraticProgram.objective
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram m n) (x : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct x P.c

theorem stationary_but_not_local_minimizer_of_negative_reduced_hessian
    {m n k : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (P : EqualityConstrainedQuadraticProgram m n)
    (hfull : HasFullRowRank P.A)
    (Z : Matrix n k ℝ)
    (hAZ : P.A * Z = 0)
    (hZspan : ∀ d : n → ℝ, P.A.mulVec d = 0 → ∃ v : k → ℝ, Z.mulVec v = d)
    (u : k → ℝ)
    (hneg : dotProduct u ((Z.transpose * P.G * Z).mulVec u) < 0)
    (xstar : n → ℝ)
    (lambdastar : m → ℝ)
    (hkkt₁ : P.G.mulVec xstar - P.A.transpose.mulVec lambdastar = fun i => -P.c i)
    (hkkt₂ : P.A.mulVec xstar = P.b) :
    P.isFeasible xstar ∧
      (∀ d : n → ℝ, P.A.mulVec d = 0 →
        dotProduct d (P.G.mulVec xstar) + dotProduct d P.c = 0) ∧
      ¬IsLocalMinOn P.objective {x | P.isFeasible x} xstar := by
  sorry

end «CAM-Bench-68»
