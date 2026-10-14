import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-136»

structure QuasiNewtonPair where
  dim : ℕ
  xj : Fin dim → ℝ
  xj1 : Fin dim → ℝ
  grad_xj : Fin dim → ℝ
  grad_xj1 : Fin dim → ℝ

def QuasiNewtonPair.s (p : QuasiNewtonPair) : ℕ → ℝ :=
  fun i => if h : i < p.dim then p.xj1 ⟨i, h⟩ - p.xj ⟨i, h⟩ else 0

def QuasiNewtonPair.y (p : QuasiNewtonPair) : ℕ → ℝ :=
  fun i => if h : i < p.dim then p.grad_xj1 ⟨i, h⟩ - p.grad_xj ⟨i, h⟩ else 0

def quasiNewtonPair {n : ℕ} (grad_f : (Fin n → ℝ) → Fin n → ℝ)
    (xj xj1 : Fin n → ℝ) : QuasiNewtonPair :=
  { dim := n
    xj := xj
    xj1 := xj1
    grad_xj := grad_f xj
    grad_xj1 := grad_f xj1 }

def IsStrictlyLowerTriangular {p : ℕ} (L : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  ∀ i j, i ≤ j → L i j = 0

theorem lower_triangular_entry_recovered_from_Qk
    (m k p n : ℕ)
    (hp : p = min k m)
    (B0 : Matrix (Fin n) (Fin n) ℝ)
    (pairs : ℕ → QuasiNewtonPair)
    (S Y Q : Matrix (Fin n) (Fin p) ℝ)
    (Lk : Matrix (Fin p) (Fin p) ℝ)
    (hS : ∀ i j, S i j = (pairs (k - p + j.1)).s i.1)
    (hY : ∀ i j, Y i j = (pairs (k - p + j.1)).y i.1)
    (hQ : Q = Y - B0 * S)
    (hL : ∀ i j, Lk i j = if i > j then ∑ t : Fin n, S t i * Y t j else 0)
    (htri : IsStrictlyLowerTriangular Lk) :
    ∀ i j, i > j →
      Lk i j =
        (∑ t : Fin n, S t i * Q t j) + (∑ a : Fin n, ∑ b : Fin n, S a i * B0 a b * S b j) := by
  sorry

end «CAM-Bench-136»
