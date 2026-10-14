import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-319»

open scoped BigOperators

structure PositiveMatrixProductMinimization (n : ℕ) where
  A : Fin n → Fin n → ℝ
  u : Fin n → ℝ
  v : Fin n → ℝ
  A_pos : ∀ i j, 0 < A i j
  u_pos : ∀ i, 0 < u i
  v_pos : ∀ i, 0 < v i

def PositiveMatrixProductMinimization.alpha {n : ℕ}
    (P : PositiveMatrixProductMinimization n) : Fin n → ℝ :=
  fun i => P.u i * P.v i

def PositiveMatrixProductMinimization.is_feasible {n : ℕ}
    (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧ ∏ i, (x i) ^ (P.alpha i) = 1

def PositiveMatrixProductMinimization.objective {n : ℕ}
    (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ) : ℝ :=
  ∏ i, (∑ j, P.A i j * x j) ^ (P.alpha i)

theorem positive_diagonal_scaling_from_optimal_solution
    {n : ℕ} (P : PositiveMatrixProductMinimization n) (x : Fin n → ℝ)
    (hx : P.is_feasible x)
    (hopt :
      ∀ y, P.is_feasible y → P.objective x ≤ P.objective y) :
    let D₁ : Fin n → ℝ := fun i => P.u i / (∑ j, P.A i j * x j)
    let D₂ : Fin n → ℝ := fun j => x j / P.u j
    (∀ i, 0 < D₁ i) ∧
    (∀ j, 0 < D₂ j) ∧
    (∀ i, D₁ i * (∑ j, P.A i j * (D₂ j * P.u j)) = P.u i) ∧
    (∀ j, ∑ i, D₁ i * P.A i j * D₂ j * P.v i = P.v j) := by
  sorry

end «CAM-Bench-319»
