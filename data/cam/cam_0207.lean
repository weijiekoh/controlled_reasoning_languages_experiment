import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-207»

def IsPermutationMatrix {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) : Prop :=
  (∀ i j, P i j = 0 ∨ P i j = 1) ∧
    (∀ i, ∑ j, P i j = 1) ∧
    ∀ j, ∑ i, P i j = 1

def IsBooleanScalar (x : ℝ) : Prop :=
  x = 0 ∨ x = 1

def IsBooleanMatrix {n : Type*} (P : Matrix n n ℝ) : Prop :=
  ∀ i j, IsBooleanScalar (P i j)

def IsAdjacencyMatrix {n : Type*} (adj : n → n → Prop)
    (A : Matrix n n ℝ) : Prop :=
  ∀ i j, (A i j = 1 ↔ adj i j) ∧ (A i j = 0 ↔ ¬ adj i j)

theorem graph_isomorphism_iff_boolean_feasibility
    {n : ℕ}
    (hn : 1 ≤ n)
    {adjA adjB : Fin n → Fin n → Prop}
    {A B P : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsAdjacencyMatrix adjA A)
    (hB : IsAdjacencyMatrix adjB B)
    (hAdjA_symm : ∀ i j, adjA i j ↔ adjA j i)
    (hAdjB_symm : ∀ i j, adjB i j ↔ adjB j i) :
    (IsPermutationMatrix P ∧ P * A * Pᵀ = B) ↔
      (IsBooleanMatrix P ∧
        (∀ i, ∑ j, P i j = 1) ∧
        (∀ j, ∑ i, P i j = 1) ∧
        A * P = P * B) := by
  sorry

end «CAM-Bench-207»
