import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-215»

def boxConstraints {n : ℕ} (l u x : Fin n → ℝ) : Prop :=
  ∀ r : Fin n, l r ≤ x r ∧ x r ≤ u r

theorem idealPreferencePointModel_iff_feasible_box_constrained_linear_system
    {K n : ℕ}
    (hK : 1 ≤ K)
    (hn : 1 ≤ n)
    (c : Fin K → Fin n → ℝ)
    (hc : ∀ k : Fin K, ∀ r : Fin n, 0 ≤ c k r ∧ c k r ≤ 1)
    (D : Set (Fin K × Fin K))
    (hD :
      ∀ i j : Fin K, i ≠ j → (((i, j) ∈ D) ↔ ((j, i) ∉ D))) :
    (∃ cIdeal : Fin n → ℝ,
      boxConstraints (fun _ => 0) (fun _ => 1) cIdeal ∧
        ∀ ⦃i j : Fin K⦄, (i, j) ∈ D →
          ‖fun r => c i r - cIdeal r‖ ≤ ‖fun r => c j r - cIdeal r‖) ↔
    (∃ cIdeal : Fin n → ℝ,
      boxConstraints (fun _ => 0) (fun _ => 1) cIdeal ∧
        ∀ ⦃i j : Fin K⦄, (i, j) ∈ D →
          2 * ∑ r : Fin n, (c j r - c i r) * cIdeal r ≤
            ∑ r : Fin n, (c j r)^2 - ∑ r : Fin n, (c i r)^2) := by
  sorry

end «CAM-Bench-215»
