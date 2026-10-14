import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-135»

open scoped Matrix

theorem Hhat_singular_of_rank_one_update
    {n : ℕ}
    (hn : 0 < n)
    (s_k y_k : Fin n → ℝ)
    (hys : dotProduct y_k s_k ≠ 0) :
    ¬Function.Bijective
      (fun x : Fin n → ℝ =>
        (((1 : Matrix (Fin n) (Fin n) ℝ) -
          Matrix.of (fun i j => s_k i * y_k j / dotProduct y_k s_k)) *ᵥ x)) := by
  sorry

end «CAM-Bench-135»
