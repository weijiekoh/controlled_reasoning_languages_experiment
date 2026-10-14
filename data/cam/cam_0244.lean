import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-244»

theorem permutation_max_norm_function_convex
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (N : Norm (Fin m → ℝ)) :
    ConvexOn ℝ Set.univ
      (fun x : Fin n → ℝ =>
        sSup
          {r : ℝ |
            ∃ P : Matrix (Fin n) (Fin n) ℝ,
              (∀ i j, P i j = 0 ∨ P i j = 1) ∧
              (∀ i, ∃! j, P i j = 1) ∧
              (∀ j, ∃! i, P i j = 1) ∧
              r = N.norm (A.mulVec (P.mulVec x) - b)}) := by
  sorry

end «CAM-Bench-244»
