import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-376»

def IsNewtonDirectionAt
    {n : ℕ}
    (hess : Matrix (Fin n) (Fin n) ℝ)
    (grad : Fin n → ℝ)
    (p : Fin n → ℝ) : Prop :=
  hess.mulVec p = fun i => -grad i

macro_rules
  | `(IsNewtonDirectionAt $hess $grad $_compat $p) =>
      `(Exercise_8_6__b_.IsNewtonDirectionAt $hess $grad $p)

def IsSymmetricTridiagonal
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ ∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → A i j = 0

def IsLinearSystem
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ)
    (b : Fin m → ℝ) : Prop :=
  A.mulVec x = b

def IsBandedCholeskyFactorization
    {n : ℕ}
    (A L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ k : ℕ,
    A.IsSymm ∧
    (∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (A.mulVec x)) ∧
    (∀ i j : Fin n, k < Int.natAbs (i.1 - j.1) → A i j = 0) ∧
    A = L * L.transpose ∧
    (∀ i j : Fin n, i.1 < j.1 → L i j = 0) ∧
    ∀ i j : Fin n, k < Int.natAbs (i.1 - j.1) → L i j = 0

def IsThomasTypeMethod
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : Prop :=

  (∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → A i j = 0) ∧

  ∃ (solve : ∀ {m : ℕ}, Matrix (Fin m) (Fin m) ℝ → (Fin m → ℝ) → Fin m → ℝ)
    (opCount : ℕ → ℕ) (C : ℕ),

    (∀ m : ℕ, opCount m ≤ C * m) ∧

    (∀ (m : ℕ) (A' : Matrix (Fin m) (Fin m) ℝ) (b' : Fin m → ℝ),
      (∀ i j : Fin m, 1 < Int.natAbs (i.1 - j.1) → A' i j = 0) →
      IsLinearSystem A' (solve A' b') b') ∧

    IsLinearSystem A (solve A b) b

theorem hessian_of_atv_objective_is_symmetric_tridiagonal_and_newton_system_linear_time
    {n : ℕ}
    (hn : 2 ≤ n)
    (x xcor : Fin n → ℝ)
    (μ ε : ℝ)
    (hμ : 0 < μ)
    (hε : 0 < ε) :
    let φ_atv : (Fin n → ℝ) → ℝ := fun y =>
      ∑ i : Fin (n - 1),
        (Real.sqrt (ε ^ 2 + (y ⟨i.1 + 1, by omega⟩ - y ⟨i.1, by omega⟩) ^ 2) - ε)
    let ψ : (Fin n → ℝ) → ℝ := fun y =>
      ‖y - xcor‖ ^ 2 + μ * φ_atv y
    let w : Fin (n - 1) → ℝ := fun i =>
      (ε ^ 2) /
        Real.rpow
          (ε ^ 2 + (x ⟨i.1 + 1, by omega⟩ - x ⟨i.1, by omega⟩) ^ 2)
          (3 / 2 : ℝ)
    let grad : Fin n → ℝ := fun i : Fin n =>
      (fderiv ℝ ψ x) (Pi.single i (1 : ℝ))
    let H : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      (fderiv ℝ (fun y => (fderiv ℝ ψ y) (Pi.single j (1 : ℝ))) x)
        (Pi.single i (1 : ℝ))
    let T : Matrix (Fin n) (Fin n) ℝ := fun i j =>
      if hdiag : i = j then
        if hi0 : i.1 = 0 then
          w ⟨0, by omega⟩
        else if hlast : i.1 + 1 = n then
          w ⟨n - 2, by omega⟩
        else
          w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩
      else if hij1 : j.1 = i.1 + 1 then
        -w ⟨i.1, by omega⟩
      else if hji1 : i.1 = j.1 + 1 then
        -w ⟨j.1, by omega⟩
      else
        0

    H = 2 • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • T ∧
    IsSymmetricTridiagonal H ∧
    (∀ i : Fin n, i.1 = 0 → T i i = w ⟨0, by omega⟩) ∧
    (∀ i : Fin n, ∀ hi1 : 1 ≤ i.1, ∀ hi2 : i.1 + 1 < n,
      T i i = w ⟨i.1 - 1, by omega⟩ + w ⟨i.1, by omega⟩) ∧
    (∀ i : Fin n, i.1 + 1 = n → T i i = w ⟨n - 2, by omega⟩) ∧
    (∀ i : Fin (n - 1), T ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩ = -w i) ∧
    (∀ i : Fin (n - 1), T ⟨i.1 + 1, by omega⟩ ⟨i.1, by omega⟩ = -w i) ∧
    (∀ i j : Fin n, 1 < Int.natAbs (i.1 - j.1) → T i j = 0) ∧

    ∀ p : Fin n → ℝ,
      IsNewtonDirectionAt H grad p →
      ((∃ L : Matrix (Fin n) (Fin n) ℝ, IsBandedCholeskyFactorization H L) ∨
        IsThomasTypeMethod H (fun i => -grad i)) := by
  sorry

end «CAM-Bench-376»
