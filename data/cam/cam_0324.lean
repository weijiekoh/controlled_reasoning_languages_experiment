import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-324»

open Matrix

structure KyFanNormSDP (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] where
  A : Matrix m n ℝ
  k : ℕ
  X : Matrix m n ℝ
  U : Matrix m m ℝ
  V : Matrix n n ℝ

def KyFanNormSDP.isFeasible
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) : Prop :=
  P.U.IsSymm ∧
  P.V.IsSymm ∧
  PosSemidef (Matrix.fromBlocks P.U P.X P.X.transpose P.V) ∧
  PosSemidef ((1 : Matrix m m ℝ) - P.U) ∧
  PosSemidef ((1 : Matrix n n ℝ) - P.V) ∧
  Matrix.trace P.U + Matrix.trace P.V = 2 * P.k

def KyFanNormSDP.objective
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (P : KyFanNormSDP m n) : ℝ :=
  Matrix.trace (P.A.transpose * P.X)

theorem kyFanNormSDP_optimal_value
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ)
    (hmn : Fintype.card n ≤ Fintype.card m)
    (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card n) :
    let fA : ℝ := sSup {r : ℝ | ∃ U : Matrix m (Fin k) ℝ, ∃ V : Matrix n (Fin k) ℝ,
      U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
        r = Matrix.trace (U.transpose * A * V)}
    (∀ P : KyFanNormSDP m n, P.A = A → P.k = k → P.isFeasible → P.objective ≤ fA) ∧
    (∀ ε > 0, ∃ P : KyFanNormSDP m n,
      P.A = A ∧ P.k = k ∧ P.isFeasible ∧ fA - ε < P.objective) := by
  sorry

end «CAM-Bench-324»
