import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-216»

theorem coordinate_values_eq_Icc_of_consistent_ideal_point
    {n K : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n)
    (c : Fin K → Fin n → ℝ)
    (observed : Set (Fin K × Fin K))
    (hobs_ne : ∀ ⦃i j : Fin K⦄, (i, j) ∈ observed → i ≠ j)
    (hobs_unique : ∀ ⦃i j : Fin K⦄, i ≠ j → ((i, j) ∈ observed ∨ (j, i) ∈ observed))
    (hc : ∀ i r, 0 ≤ c i r ∧ c i r ≤ 1)
    (hnonempty :
      ∃ x : Fin n → ℝ,
        (∀ r, 0 ≤ x r ∧ x r ≤ 1) ∧
        ∀ ⦃i j : Fin K⦄, (i, j) ∈ observed →
          ‖c i - x‖ ≤ ‖c j - x‖) :
    ∀ r : Fin n,
      let S : Set (Fin n → ℝ) :=
        {x |
          (∀ s, 0 ≤ x s ∧ x s ≤ 1) ∧
          ∀ ⦃i j : Fin K⦄, (i, j) ∈ observed → ‖c i - x‖ ≤ ‖c j - x‖}
      let m : Fin n → ℝ := fun s => sInf ((fun x : Fin n → ℝ => x s) '' S)
      let M : Fin n → ℝ := fun s => sSup ((fun x : Fin n → ℝ => x s) '' S)
      (fun x : ℝ => ∃ y ∈ S, y r = x) = Set.Icc (m r) (M r) := by
  sorry

end «CAM-Bench-216»
