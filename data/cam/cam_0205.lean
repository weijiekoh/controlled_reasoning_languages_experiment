import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-205»

def DirectedAcyclicGraph {V : Type _} (adj : V → V → Prop) : Prop :=
  ¬ ∃ (v : V) (n : ℕ), 0 < n ∧ ∃ (f : Fin (n + 1) → V), f 0 = v ∧ f ⟨n, Nat.lt_succ_self n⟩ = v ∧
    ∀ i : Fin n, adj (f ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩) (f ⟨i.1.succ, Nat.succ_lt_succ i.2⟩)

structure ConvexInterdictionProblem where
  n : ℕ
  m : ℕ
  hn : 0 < n
  edge : Fin m → Fin n → Fin n → Prop
  a : Fin m → ℝ
  xmax : Fin m → ℝ
  B : ℝ

theorem interdiction_minimization_equivalent_to_convex_problem
    (n m : ℕ) (hn : 0 < n)
    (edge : Fin m → Fin n → Fin n → Prop)
    (a xmax : Fin m → ℝ) (B : ℝ)
    (hdag : DirectedAcyclicGraph (fun u v : Fin n => ∃ j : Fin m, edge j u v))
    (hpos_a : ∀ j : Fin m, 0 < a j)
    (hpos_xmax : ∀ j : Fin m, 0 ≤ xmax j)
    (hpos_B : 0 ≤ B)
    (hpath : Nonempty
      (Σ ℓ : ℕ, {f : Fin (ℓ + 1) → Fin n //
        (∀ h : 0 < n, f 0 = ⟨0, h⟩) ∧
        (∃ h' : 0 < n,
          f ⟨ℓ, Nat.lt_succ_self ℓ⟩ = ⟨n - 1, Nat.sub_lt h' (by simp)⟩) ∧
        (∀ i : Fin ℓ, ∃ j : Fin m, edge j
          (f ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self ℓ)⟩)
          (f ⟨i.1.succ, Nat.succ_lt_succ i.2⟩))})) :
    sInf
      {r : ℝ |
        ∃ x : Fin m → ℝ, ∃ P : Fin n → ℝ,
          (∀ i : Fin n, 0 < P i) ∧
          P ⟨0, hn⟩ = 1 ∧
          (∀ j : Fin m, 0 ≤ x j ∧ x j ≤ xmax j) ∧
          (∑ j : Fin m, x j) ≤ B ∧
          (∀ i : Fin n,
            i ≠ ⟨0, hn⟩ →
              P i =
                sSup {t : ℝ | ∃ j : Fin m, ∃ k : Fin n,
                  edge j k i ∧ t = P k * Real.exp (-a j * x j)}) ∧
          r = Real.log (P ⟨n - 1, Nat.sub_lt hn (by simp)⟩)} =
    sInf
      {r : ℝ |
        ∃ x : Fin m → ℝ, ∃ y : Fin n → ℝ,
          y ⟨0, hn⟩ = 0 ∧
          (∀ j : Fin m, ∀ k i : Fin n, edge j k i → y i ≥ y k - a j * x j) ∧
          (∀ j : Fin m, 0 ≤ x j ∧ x j ≤ xmax j) ∧
          (∑ j : Fin m, x j) ≤ B ∧
          r = y ⟨n - 1, Nat.sub_lt hn (by simp)⟩} := by
  sorry

end «CAM-Bench-205»
