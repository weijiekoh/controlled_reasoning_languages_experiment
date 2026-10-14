import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-220»

def nodeEdgeIncidenceMatrix (n m : ℕ) (tail head : Fin m → Fin n) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j =>
    if i = head j then
      1
    else if i = tail j then
      -1
    else
      0

theorem supportableConsumptionSet_isPolyhedron_and_characterization
    (n m k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : k ≤ n)
    (tail head : Fin m → Fin n)
    (h : Fin n → ℝ)
    (alpha0 : ℝ)
    (halpha0 : 0 < alpha0)
    (L R : Fin m → ℝ)
    (hL : ∀ j, 0 < L j)
    (hR : ∀ j, 0 < R j)
    (edge_descends : ∀ j, h (tail j) > h (head j))
    (smax : Fin k → ℝ)
    (hsmax : ∀ i, 0 ≤ smax i)
    (c : Fin (n - k) → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    let A := nodeEdgeIncidenceMatrix n m tail head
    let edgeCapacity : Fin m → ℝ := fun j => alpha0 * (R j)^2 * (h (tail j) - h (head j)) / (L j)
    let supportable : Set (Fin (n - k) → ℝ) := fun c' =>
      ∃ f : Fin m → ℝ, ∃ s : Fin k → ℝ, ∃ theta : Fin m → ℝ,
        (∀ j, 0 ≤ f j) ∧
        (∀ i, 0 ≤ s i ∧ s i ≤ smax i) ∧
        (∀ j, 0 ≤ theta j ∧ theta j ≤ 1) ∧
        (∀ i : Fin k,
          ∑ j : Fin m, A ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩ j * f j = - s i) ∧
        (∀ i : Fin (n - k),
          ∑ j : Fin m, A ⟨k + i.1, by
            have hi : i.1 < n - k := i.2
            omega⟩ j * f j = c' i) ∧
        (∀ j, f j = edgeCapacity j * theta j)
    (∃ p q : ℕ,
      ∃ M : Matrix (Fin p) (Fin (n - k)) ℝ,
        ∃ N : Matrix (Fin q) (Fin (n - k)) ℝ,
          ∃ b : Fin p → ℝ,
            ∃ d : Fin q → ℝ,
              (∀ c' : Fin (n - k) → ℝ,
                c' ∈ supportable ↔
                  (∀ i : Fin p, ∑ j : Fin (n - k), M i j * c' j ≤ b i) ∧
                  (∀ i : Fin q, ∑ j : Fin (n - k), N i j * c' j = d i)) ∧
              (c ∈ supportable ↔
                (∀ i : Fin p, ∑ j : Fin (n - k), M i j * c j ≤ b i) ∧
                (∀ i : Fin q, ∑ j : Fin (n - k), N i j * c j = d i))) := by
  sorry

end «CAM-Bench-220»
