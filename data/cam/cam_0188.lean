import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-188»

structure WorstCaseProfitLinearProgram where
  n : ℕ
  m : ℕ
  p : Fin n → ℝ
  q : Fin n → ℝ
  S : Fin n → Finset (Fin m)

def WorstCaseProfitLinearProgram.IsFeasible
    (P : WorstCaseProfitLinearProgram) (x : Fin P.n → ℝ) (t : ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ P.q i) ∧
    ∀ j : Fin P.m, t ≤
      (∑ i : Fin P.n, P.p i * x i) -
      ∑ i : { i : Fin P.n // j ∈ P.S i }, x i.1

theorem worstCaseProfit_maximization_iff_linearProgram_optimal
    (P : WorstCaseProfitLinearProgram)
    (hm : 1 ≤ P.m)
    (hn : 1 ≤ P.n)
    (hq : ∀ i : Fin P.n, 0 < P.q i)
    (hp : ∀ i : Fin P.n, 0 < P.p i)
    (x : Fin P.n → ℝ)
    (hx : ∀ i : Fin P.n, 0 ≤ x i ∧ x i ≤ P.q i) :
    let worstCaseProfit : (Fin P.n → ℝ) → ℝ :=
      fun x' =>
        Finset.inf' (Finset.univ : Finset (Fin P.m))
          (by
            have hm0 : 0 < P.m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
            exact ⟨⟨0, hm0⟩, Finset.mem_univ _⟩)
          (fun j : Fin P.m =>
            (∑ i : Fin P.n, P.p i * x' i) -
              ∑ i : { i : Fin P.n // j ∈ P.S i }, x' i.1)
    ((∀ x' : Fin P.n → ℝ,
        (∀ i : Fin P.n, 0 ≤ x' i ∧ x' i ≤ P.q i) →
          worstCaseProfit x' ≤ worstCaseProfit x) ↔
      ∃ t : ℝ,
        P.IsFeasible x t ∧
          ∀ x' : Fin P.n → ℝ, ∀ t' : ℝ, P.IsFeasible x' t' → t' ≤ t) := by
  sorry

end «CAM-Bench-188»
