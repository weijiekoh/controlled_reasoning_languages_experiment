import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-356»

theorem range_nonneg_eq_univ_iff_feasible_pm_stdBasis
    {n k : ℕ} (A : Fin n → Fin k → ℝ) :
    ((Set.range fun x : Fin k → ℝ =>
        (fun i : Fin n => ∑ j : Fin k, A i j * x j)) =
      (Set.univ : Set (Fin n → ℝ))) ↔
      (∀ i : Fin n,
        (∃ x : Fin k → ℝ,
          (∀ j : Fin k, 0 ≤ x j) ∧
            (fun r : Fin n => ∑ j : Fin k, A r j * x j) = Pi.single i 1) ∧
        ∃ x : Fin k → ℝ,
          (∀ j : Fin k, 0 ≤ x j) ∧
            (fun r : Fin n => ∑ j : Fin k, A r j * x j) = Pi.single i (-1)) := by
  sorry

end «CAM-Bench-356»
