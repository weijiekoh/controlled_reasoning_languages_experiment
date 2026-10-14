import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-739»

def IsLocalMinimizer {E β : Type*} [NormedAddCommGroup E] [Preorder β] (f : E → β) (zStar : E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ z : E, ‖z - zStar‖ < ε → f zStar ≤ f z

structure LowRankMatrixFactorizationProblem (m n r : Type*)
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r] where
  A : Matrix m n ℝ

def LowRankMatrixFactorizationProblem.objective
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (p : LowRankMatrixFactorizationProblem m n r) (X : Matrix m r ℝ) (Y : Matrix r n ℝ) : ℝ :=
  ‖p.A - X * Y‖ ^ 2

def LowRankMatrixFactorizationProblem.isOptimal
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype r] [DecidableEq r]
    (p : LowRankMatrixFactorizationProblem m n r) (X : Matrix m r ℝ) (Y : Matrix r n ℝ) : Prop :=
  ∀ X' : Matrix m r ℝ, ∀ Y' : Matrix r n ℝ,
    p.objective X Y ≤ p.objective X' Y'

open scoped RealInnerProductSpace

theorem lowRankMatrixFactorization_localMinimizer_necessary_conditions
    {m n r : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    [InnerProductSpace ℝ (Matrix m r ℝ × Matrix r n ℝ)]
    (p : LowRankMatrixFactorizationProblem m n r)
    (XStar : Matrix m r ℝ) (YStar : Matrix r n ℝ)
    (hloc :
      IsLocalMinimizer
        (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
          ‖p.A - Z.1 * Z.2‖ ^ 2)
        (XStar, YStar)) :
    fderiv ℝ (fun X : Matrix m r ℝ => ‖p.A - X * YStar‖ ^ 2) XStar = 0 ∧
      fderiv ℝ (fun Y : Matrix r n ℝ => ‖p.A - XStar * Y‖ ^ 2) YStar = 0 ∧
      (ContDiffAt ℝ 2
          (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
            ‖p.A - Z.1 * Z.2‖ ^ 2)
          (XStar, YStar) →
        ∀ d : Matrix m r ℝ × Matrix r n ℝ,
          0 ≤
            ⟪d,
              (fderiv ℝ
                (gradient
                  (fun Z : Matrix m r ℝ × Matrix r n ℝ =>
                    ‖p.A - Z.1 * Z.2‖ ^ 2))
                (XStar, YStar)) d⟫) := by
  sorry

end «CAM-Bench-739»
