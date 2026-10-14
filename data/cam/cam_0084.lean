import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-84»

def primalLogBarrier {α : Type*} {ι : Type*} [Fintype ι]
    (f : α → ℝ) (g : ι → α → ℝ) (μ : ℝ) (x : α)
    (_hμ : 0 < μ) (_hx : ∀ i : ι, 0 < g i x) : ℝ :=
  f x - μ * ∑ i, Real.log (g i x)

structure ScalarLinearProgram where
  x : ℝ

def ScalarLinearProgram.objective (p : ScalarLinearProgram) : ℝ := p.x

def ScalarLinearProgram.is_feasible (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1

def scalarLogBarrierObjective (μ x : ℝ) : ℝ :=
  x - μ * Real.log x - μ * Real.log (1 - x)

theorem scalarLinearProgram_primalLogBarrier_eq
    (μ x : ℝ) (hμ : 0 < μ) (hx0 : 0 < x) (hx1 : x < 1) :
    primalLogBarrier (α := ℝ) (ι := Fin 2)
      (fun y => y)
      (fun i y => if i = 0 then y else 1 - y)
      μ x
      hμ
      (by
        intro i
        fin_cases i
        · simpa using hx0
        · simpa using sub_pos.mpr hx1)
      =
      scalarLogBarrierObjective μ x ∧
    deriv (scalarLogBarrierObjective μ) x = 1 - μ / x + μ / (1 - x) ∧
    (deriv (scalarLogBarrierObjective μ) x = 0 ↔
      x ^ 2 - (1 + 2 * μ) * x + μ = 0) := by
  sorry

end «CAM-Bench-84»
