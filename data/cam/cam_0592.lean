import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-592»

structure LinearProgram (m p n : ℕ) where
  c : Fin n → ℝ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  E : Fin p → Fin n → ℝ
  d : Fin p → ℝ

def LinearProgram.isFeasible {m p n : ℕ} (P : LinearProgram m p n) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≤ P.b i) ∧
    ∀ i : Fin p, ∑ j : Fin n, P.E i j * x j = P.d i

def LinearProgram.objective {n : ℕ} (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, c j * x j

def linearProgram {m p n : ℕ} (c : Fin n → ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (E : Fin p → Fin n → ℝ) (d : Fin p → ℝ) : LinearProgram m p n :=
  { c := c, A := A, b := b, E := E, d := d }

structure EquivalentLinearProgram (N : ℕ) where
  H : Fin N → Fin N → ℝ
  xDes : Fin N → ℝ

def EquivalentLinearProgram.isFeasible {N : ℕ}
    (P : EquivalentLinearProgram N) (u y t : Fin N → ℝ) : Prop :=
  (∀ i : Fin N, ∑ j : Fin N, P.H i j * u j = P.xDes i) ∧
    (∀ i : Fin N, -y i ≤ u i) ∧
    (∀ i : Fin N, u i ≤ y i) ∧
    (∀ i : Fin N, y i ≤ t i) ∧
    ∀ i : Fin N, 2 * y i - 1 ≤ t i

def EquivalentLinearProgram.objectiveValue {N : ℕ} (t : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, t i

theorem sparse_control_problem_equivalent_to_equivalentLinearProgram
    {N n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xDes : Fin n → ℝ) :
    let P : EquivalentLinearProgram N :=
      { H := fun i j => if h : i.1 < n then ((A ^ (N - 1 - j.1)) *ᵥ b) ⟨i.1, h⟩ else 0
        xDes := fun i => if h : i.1 < n then xDes ⟨i.1, h⟩ else 0 }
    (∀ u : Fin N → ℝ,
      (∃ x : Fin (N + 1) → Fin n → ℝ,
        x 0 = 0 ∧
        (∀ t : Fin N,
          x t.succ =
            fun i => (∑ j : Fin n, A i j * x (Fin.castSucc t) j) + b i * u t) ∧
        x (Fin.last N) = xDes) ↔
      ∃ y t : Fin N → ℝ, P.isFeasible u y t) ∧
    (∀ u : Fin N → ℝ, ∀ y t : Fin N → ℝ,
      P.isFeasible u y t →
      EquivalentLinearProgram.objectiveValue t =
        ∑ i : Fin N, if |u i| ≤ 1 then |u i| else 2 * |u i| - 1) := by
  sorry

end «CAM-Bench-592»
