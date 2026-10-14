import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-467»

theorem dualCone_Kmplus_eq_partialSums_nonneg (n : ℕ) (hn : 0 < n) :
    (let Kmplus : Set (Fin n → ℝ) :=
      {x : Fin n → ℝ |
        (∀ i j : Fin n, i ≤ j → x j ≤ x i) ∧ ∀ i : Fin n, 0 ≤ x i}
    let dualCone : Set (Fin n → ℝ) → Set (Fin n → ℝ) := fun K =>
      {y : Fin n → ℝ | ∀ x : Fin n → ℝ, x ∈ K → 0 ≤ ∑ i : Fin n, y i * x i}
    dualCone Kmplus) =
    {y : Fin n → ℝ |
      ∀ k : ℕ, 1 ≤ k → k ≤ n → 0 ≤ ∑ i : Fin n, if (i : ℕ) < k then y i else 0} := by
  sorry

end «CAM-Bench-467»
