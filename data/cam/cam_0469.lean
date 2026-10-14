import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-469»

def IsLinearOrdering {S : Type} (r : S → S → Prop) : Prop :=
  (∀ x : S, r x x) ∧
    (∀ x y : S, r x y → r y x → x = y) ∧
      (∀ x y z : S, r x y → r y z → r x z) ∧
        (∀ x y : S, r x y ∨ r y x)

open scoped BigOperators

theorem lex_preorder_isLinearOrdering (n : ℕ) (hn : 1 ≤ n) :
    IsLinearOrdering (S := (Fin n → ℝ)) (fun x y => y - x ∈
      ({0} : Set (Fin n → ℝ)) ∪
        {x | ∃ k : Fin n,
          (∀ i : Fin n, (i : ℕ) < (k : ℕ) → x i = 0) ∧ x k > 0}) := by
  sorry

end «CAM-Bench-469»
