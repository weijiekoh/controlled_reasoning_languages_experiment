import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-217»

def extendedRealOptimalValue (f : α → ℝ) (X : Set α) : EReal :=
  sInf ((fun z => (f z : EReal)) '' X)

def transportDistance (C : Fin n → Fin n → EReal) (a b : Fin n → ℝ) : EReal :=
  sInf
    {r | ∃ S : Fin n → Fin n → ℝ,
      (∀ i j, 0 ≤ S i j) ∧
      (∀ i, ∑ j, S i j = b i) ∧
      (∀ j, ∑ i, S i j = a j) ∧
      r =
        (∑ i, ∑ j,
          if C i j = ⊤ then
            if 0 < S i j then (⊤ : EReal) else 0
          else
            C i j * (S i j : EReal))}

theorem transportDistance_basic_properties
    (n : ℕ) (hn : 1 ≤ n)
    (C : Fin n → Fin n → EReal)
    (hC_diag : ∀ i, C i i = 0)
    (hC_symm : ∀ i j, i ≠ j → C i j = C j i)
    (hC_pos : ∀ i j, i ≠ j → 0 < C i j) :
    ∀ x y : Fin n → ℝ,
      (∑ i, x i = 1) →
      (∑ i, y i = 1) →
      (∀ i, 0 ≤ x i) →
      (∀ i, 0 ≤ y i) →
      transportDistance C x y = transportDistance C y x ∧
      0 ≤ transportDistance C x y ∧
      transportDistance C x x = 0 ∧
      (x ≠ y → 0 < transportDistance C x y) := by
  sorry

end «CAM-Bench-217»
