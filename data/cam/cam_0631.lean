import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-631»

def feasible {α : Type*} (C : Set α) (x : α) : Prop := x ∈ C

def optimalSolution {α : Type*} (f : α → ℝ) (C : Set α) (xStar : α) : Prop :=
  feasible C xStar ∧ ∀ x, feasible C x → f xStar ≤ f x

def optimalValue {α : Type*} (f : α → ℝ) (C : Set α) : EReal :=
  sInf ((fun x => (f x : EReal)) '' C)

structure BoundedLinearProgram where
  n : ℕ
  c : Fin n → ℝ
  d : Fin n → ℝ
  α : ℝ

def BoundedLinearProgram.feasibleSet (P : BoundedLinearProgram) : Set (Fin P.n → ℝ) :=
  {x | (∑ i, P.d i * x i = P.α) ∧ ∀ i, 0 ≤ x i ∧ x i ≤ 1}

def BoundedLinearProgram.objective (P : BoundedLinearProgram) (x : Fin P.n → ℝ) : ℝ :=
  ∑ i, P.c i * x i

def BoundedLinearProgram.isFeasible (P : BoundedLinearProgram) (x : Fin P.n → ℝ) : Prop :=
  x ∈ P.feasibleSet

theorem boundedLinearProgram_greedy_optimal_solution
    (P : BoundedLinearProgram)
    (hpos : ∀ i, 0 < P.d i)
    (hα_nonneg : 0 ≤ P.α)
    (hα_le : P.α ≤ ∑ i, P.d i)
    (hmono : ∀ i j : Fin P.n, i ≤ j → P.c i / P.d i ≤ P.c j / P.d j)
    (k : ℕ)
    (hk_le_n : k ≤ P.n)
    (hsum_le :
      (Finset.univ.sum (fun i : Fin k =>
        P.d ⟨i.1, Nat.lt_of_lt_of_le i.2 hk_le_n⟩)) ≤ P.α)
    (hsum_succ_gt : ∀ hk_lt_n : k < P.n,
      P.α <
        (Finset.univ.sum (fun i : Fin (k + 1) =>
          P.d ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt hk_lt_n)⟩)))
    (hk_max :
      ∀ m, ∀ hm_le_n : m ≤ P.n,
        (Finset.univ.sum (fun i : Fin m =>
          P.d ⟨i.1, Nat.lt_of_lt_of_le i.2 hm_le_n⟩)) ≤ P.α →
        m ≤ k) :
    (∃ xStar : Fin P.n → ℝ,
      (∀ i,
        xStar i =
          if h1 : i.1 + 1 ≤ k then
            1
          else if h2 : i.1 + 1 = k + 1 then
            if hk_lt_n : k < P.n then
              (P.α -
                Finset.univ.sum (fun j : Fin k =>
                  P.d ⟨j.1, Nat.lt_of_lt_of_le j.2 hk_le_n⟩)) / P.d ⟨k, hk_lt_n⟩
            else
              0
          else
            0) ∧
      P.isFeasible xStar ∧
      optimalSolution P.objective {x | P.isFeasible x} xStar ∧
      ((∀ hk_lt_n : k < P.n,
          P.objective xStar =
            (Finset.univ.sum (fun i : Fin k =>
              P.c ⟨i.1, Nat.lt_of_lt_of_le i.2 hk_le_n⟩) +
              (P.c ⟨k, hk_lt_n⟩ / P.d ⟨k, hk_lt_n⟩) *
                (P.α -
                  Finset.univ.sum (fun i : Fin k =>
                    P.d ⟨i.1, Nat.lt_of_lt_of_le i.2 hk_le_n⟩)))) ∧
       (∀ hk_eq_n : k = P.n, P.objective xStar = ∑ i, P.c i))) := by
  sorry

end «CAM-Bench-631»
