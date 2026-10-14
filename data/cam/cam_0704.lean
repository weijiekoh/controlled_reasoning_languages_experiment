import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-704»

structure VectorNorm (n : ℕ) where
  norm : (Fin n → ℝ) → ℝ
  nonneg : ∀ x : Fin n → ℝ, 0 ≤ norm x
  eq_zero_iff : ∀ x : Fin n → ℝ, norm x = 0 ↔ x = 0
  smul : ∀ (a : ℝ) (x : Fin n → ℝ), norm (a • x) = |a| * norm x
  add_le : ∀ x y : Fin n → ℝ, norm (x + y) ≤ norm x + norm y

def IsDualNormValue {n : ℕ} (N : VectorNorm n) (y : Fin n → ℝ) (value : ℝ) : Prop :=
  (∀ d : Fin n → ℝ, N.norm d ≤ 1 → dotProduct y d ≤ value) ∧
    ∀ ε : ℝ, 0 < ε → ∃ d : Fin n → ℝ, N.norm d ≤ 1 ∧ value < dotProduct y d + ε

def IsNormalizedSteepestDescentDirection {n : ℕ}
    (N : VectorNorm n)
    (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (hfdiff : DifferentiableAt ℝ f x)
    (Δx_nsd : Fin n → ℝ) : Prop :=
  N.norm Δx_nsd ≤ 1 ∧
    ∀ d : Fin n → ℝ, N.norm d ≤ 1 →
      dotProduct (fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) Δx_nsd ≤
        dotProduct (fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) d

def IsSteepestDescentDirection {n : ℕ}
    (N : VectorNorm n)
    (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ)
    (hfdiff : DifferentiableAt ℝ f x)
    (p : Fin n → ℝ) : Prop :=
  p ≠ 0 ∧
    ∀ d : Fin n → ℝ,
      d ≠ 0 →
        dotProduct (fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) p / N.norm p ≤
          dotProduct (fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))) d / N.norm d

theorem normalizedSteepestDescentDirection_eq_neg_dualNorm {n : ℕ}
    (N : VectorNorm n)
    (f : (Fin n → ℝ) → ℝ)
    (x Δx_nsd : Fin n → ℝ)
    (dual : ℝ)
    (hfdiff : DifferentiableAt ℝ f x)
    (hdual :
      IsDualNormValue N
        (fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ)))
        dual)
    (hnsd : IsNormalizedSteepestDescentDirection N f x hfdiff Δx_nsd) :
    let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
    dotProduct grad Δx_nsd = -dual := by
  sorry

end «CAM-Bench-704»
