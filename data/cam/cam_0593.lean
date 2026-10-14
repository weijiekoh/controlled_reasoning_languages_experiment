import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-593»

structure PiecewiseLinearRevenueMaximization where
  m : ℕ
  n : ℕ
  A : Matrix (Fin m) (Fin n) ℝ
  cMax : Fin m → ℝ
  p : Fin n → ℝ
  q : Fin n → ℝ
  pDisc : Fin n → ℝ
  p_pos : ∀ j, 0 < p j
  q_pos : ∀ j, 0 < q j
  pDisc_pos : ∀ j, 0 < pDisc j
  pDisc_lt_p : ∀ j, pDisc j < p j

def PiecewiseLinearRevenueMaximization.revenueAt
    (P : PiecewiseLinearRevenueMaximization) (j : Fin P.n) (xj : ℝ) : ℝ :=
  if xj ≤ P.q j then
    P.p j * xj
  else
    P.p j * P.q j + P.pDisc j * (xj - P.q j)

def PiecewiseLinearRevenueMaximization.feasible
    (P : PiecewiseLinearRevenueMaximization) (x : Fin P.n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ P.A.mulVec x ≤ P.cMax

def PiecewiseLinearRevenueMaximization.objective
    (P : PiecewiseLinearRevenueMaximization) (x : Fin P.n → ℝ) : ℝ :=
  ∑ j, P.revenueAt j (x j)

structure PiecewiseLinearRevenueEpigraphLP where
  data : PiecewiseLinearRevenueMaximization

def PiecewiseLinearRevenueEpigraphLP.feasible
    (P : PiecewiseLinearRevenueEpigraphLP)
    (x u : Fin P.data.n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧
    (∀ i, (∑ j, P.data.A i j * x j) ≤ P.data.cMax i) ∧
    (∀ j, u j ≤ P.data.p j * x j) ∧
    (∀ j, u j ≤ P.data.p j * P.data.q j + P.data.pDisc j * (x j - P.data.q j))

def PiecewiseLinearRevenueEpigraphLP.objective
    (P : PiecewiseLinearRevenueEpigraphLP)
    (u : Fin P.data.n → ℝ) : ℝ :=
  ∑ j, u j

theorem piecewiseLinearRevenue_equivalent_to_epigraphLP
    (P : PiecewiseLinearRevenueMaximization) :
    (∀ x : Fin P.n → ℝ,
      P.feasible x →
        ((P.objective x : ℝ) : EReal) =
          sSup
            {s : EReal |
              ∃ u : Fin P.n → ℝ,
                (∀ j, u j ≤ P.p j * x j) ∧
                (∀ j, u j ≤ P.p j * P.q j + P.pDisc j * (x j - P.q j)) ∧
                s = ((∑ j, u j : ℝ) : EReal)}) ∧
    sSup {v : EReal | ∃ x : Fin P.n → ℝ, P.feasible x ∧ v = ((P.objective x : ℝ) : EReal)} =
      sSup
        {v : EReal |
          ∃ x : Fin P.n → ℝ,
            ∃ u : Fin P.n → ℝ,
              PiecewiseLinearRevenueEpigraphLP.feasible ⟨P⟩ x u ∧
              v = ((PiecewiseLinearRevenueEpigraphLP.objective ⟨P⟩ u : ℝ) : EReal)} := by
  sorry

end «CAM-Bench-593»
