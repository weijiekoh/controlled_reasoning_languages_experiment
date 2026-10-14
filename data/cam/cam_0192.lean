import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-192»

def bisection (α : Type*) [LinearOrder α] (feasible : α → Prop) (ℓ u : α) : Prop :=
  ℓ ≤ u ∧ ∃ t, ℓ ≤ t ∧ t ≤ u ∧ ∀ x, ℓ ≤ x ∧ x ≤ u → (feasible x ↔ t ≤ x)

open scoped Matrix

theorem minimum_time_rope_transfer_feasible_by_bisection
    (m h Tmax θ : ℝ)
    (hm : 0 < m)
    (hh : 0 < h)
    (hTmax : 0 ≤ Tmax)
    (p_init p_des : Fin 2 → ℝ)
    (hp_init_des : p_init = p_des) :
    bisection ℕ
      (fun k =>
        1 ≤ k ∧
        ∃ p : Fin k → (Fin 2 → ℝ),
          ∃ v : Fin k → (Fin 2 → ℝ),
            ∃ F : Fin (k - 1) → (Fin 2 → ℝ),
              ∃ Tleft : Fin (k - 1) → ℝ,
                ∃ Tright : Fin (k - 1) → ℝ,
                  (∀ i, 0 ≤ Tleft i ∧ Tleft i ≤ Tmax) ∧
                  (∀ i, 0 ≤ Tright i ∧ Tright i ≤ Tmax) ∧
                  (∀ i,
                    F i =
                      fun j =>
                        Tleft i * ![-Real.sin θ, Real.cos θ] j +
                        Tright i * ![Real.sin θ, Real.cos θ] j +
                        m * ![0, -9.8] j) ∧
                  (∀ i : Fin (k - 1),
                    ∃ hi : i.1 + 1 < k,
                    p ⟨i.1 + 1, hi⟩ =
                      fun j => p ⟨i.1, Nat.lt_of_lt_of_le i.is_lt (Nat.sub_le _ _)⟩ j +
                        h * v ⟨i.1, Nat.lt_of_lt_of_le i.is_lt (Nat.sub_le _ _)⟩ j) ∧
                  (∀ i : Fin (k - 1),
                    ∃ hi : i.1 + 1 < k,
                    v ⟨i.1 + 1, hi⟩ =
                      fun j =>
                        v ⟨i.1, Nat.lt_of_lt_of_le i.is_lt (Nat.sub_le _ _)⟩ j +
                        (h / m) * F i j) ∧
                  (∃ hk : 0 < k,
                    p ⟨0, hk⟩ = p_init ∧
                    p ⟨k - 1, by omega⟩ = p_des ∧
                    v ⟨0, hk⟩ = ![0, 0] ∧
                    v ⟨k - 1, by omega⟩ = ![0, 0]))
      1 1 := by
  sorry

end «CAM-Bench-192»
