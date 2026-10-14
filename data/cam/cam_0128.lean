import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-128»

open Matrix

theorem trace_bfgs_update
    {n : Type*} [Fintype n] [DecidableEq n]
    (Bₖ : Matrix n n ℝ) (sₖ yₖ : n → ℝ)
    (h_symm : Bₖ.IsSymm)
    (hBs : dotProduct sₖ (Bₖ.mulVec sₖ) ≠ 0)
    (hys : dotProduct yₖ sₖ ≠ 0) :
    Matrix.trace
        (Bₖ
          - ((1 / dotProduct sₖ (Bₖ.mulVec sₖ)) •
              (vecMulVec (Bₖ.mulVec sₖ) (Bₖ.mulVec sₖ)))
          + ((1 / dotProduct yₖ sₖ) • vecMulVec yₖ yₖ))
      =
      Matrix.trace Bₖ
        - (dotProduct (Bₖ.mulVec sₖ) (Bₖ.mulVec sₖ)) / (dotProduct sₖ (Bₖ.mulVec sₖ))
        + (dotProduct yₖ yₖ) / (dotProduct yₖ sₖ) := by
  sorry

end «CAM-Bench-128»
