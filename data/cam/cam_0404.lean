import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-404»

def IsEqualityConstrainedNewtonStep
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (f : (n → ℝ) → ℝ)
    (fgrad : (n → ℝ) → n → ℝ)
    (fhess : (n → ℝ) → Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (b : m → ℝ)
    (x : n → ℝ)
    (Δx : n → ℝ) : Prop :=
  A.mulVec x = b ∧
    ∃ w : m → ℝ,
      (Matrix.fromBlocks (fhess x) A.transpose A (0 : Matrix m m ℝ)).mulVec
          (Sum.elim Δx w) =
        Sum.elim (-(fgrad x)) (0 : m → ℝ)

def IsEqualityConstrainedProblem
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (A : Matrix m n ℝ)
    (b : m → ℝ)
    (x : n → ℝ) : Prop :=
  A.mulVec x = b

theorem equalityConstrainedNewtonSteps_same_for_quadraticPenalty
    {n m : Type*}
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m]
    (f : (n → ℝ) → ℝ)
    (fgrad : (n → ℝ) → n → ℝ)
    (fhess : (n → ℝ) → Matrix n n ℝ)
    (A : Matrix m n ℝ)
    (b : m → ℝ)
    (Q : Matrix m m ℝ)
    (hQsymm : Q.IsSymm)
    (hQpsd : ∀ y : m → ℝ, 0 ≤ y ⬝ᵥ Q.mulVec y)
    (x : n → ℝ)
    (Δx : n → ℝ) :
    IsEqualityConstrainedNewtonStep f fgrad fhess A b x Δx ↔
      (A.mulVec x = b ∧
        ∃ w' : m → ℝ,
          (Matrix.fromBlocks
              (fhess x + 2 • (A.transpose * Q * A))
              A.transpose
              A
              (0 : Matrix m m ℝ)).mulVec
              (Sum.elim Δx w') =
            Sum.elim (-(fgrad x) - 2 • ((A.transpose * Q).mulVec (A.mulVec x - b))) (0 : m → ℝ)) := by
  sorry

end «CAM-Bench-404»
