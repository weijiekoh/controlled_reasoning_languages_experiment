import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-712»

def JointlyConvex
    {E₁ E₂ : Type*}
    [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (C₁ : Set E₁) (C₂ : Set E₂) (f : E₁ × E₂ → EReal) : Prop :=
  ∀ ⦃x₁ x₂ : E₁⦄, x₁ ∈ C₁ → x₂ ∈ C₁ →
    ∀ ⦃y₁ y₂ : E₂⦄, y₁ ∈ C₂ → y₂ ∈ C₂ →
    ∀ ⦃θ : ℝ⦄, 0 ≤ θ → θ ≤ 1 →
      f (θ • x₁ + (1 - θ) • x₂, θ • y₁ + (1 - θ) • y₂) ≤
        θ * f (x₁, y₁) + (1 - θ) * f (x₂, y₂)

structure SemidefiniteProgram (n p : ℕ) where
  X : Matrix (Fin n) (Fin n) ℝ
  symmetric : Xᵀ = X
  objective : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ
  F0 : Matrix (Fin n) (Fin n) ℝ
  x : Fin p → ℝ
  F : Fin p → Matrix (Fin n) (Fin n) ℝ

def SemidefiniteProgram.lmiMatrix {n p : ℕ} (sdp : SemidefiniteProgram n p) :
    Matrix (Fin n) (Fin n) ℝ :=
  sdp.F0 + ∑ i : Fin p, sdp.x i • sdp.F i

def SemidefiniteProgram.objectiveValue {n p : ℕ} (sdp : SemidefiniteProgram n p) : ℝ :=
  sdp.objective sdp.X

def SemidefiniteProgram.IsFeasible {n p : ℕ} (sdp : SemidefiniteProgram n p) : Prop :=
  sdp.X = sdp.lmiMatrix ∧ sdp.X.PosSemidef

structure TraceMinimizationSDP (m n : ℕ) where
  A : Matrix (Fin m) (Fin m) ℝ
  A_posDef : A.PosDef
  B : Matrix (Fin m) (Fin n) ℝ
  X : Matrix (Fin n) (Fin n) ℝ
  X_isSymm : X.IsSymm

def TraceMinimizationSDP.objective {m n : ℕ} (p : TraceMinimizationSDP m n) : ℝ :=
  Matrix.trace p.X

def TraceMinimizationSDP.blockMatrix {m n : ℕ} (p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  Matrix.fromBlocks p.A p.B p.B.transpose X

def TraceMinimizationSDP.isFeasible {m n : ℕ} (p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧ (p.blockMatrix X).PosSemidef

def TraceMinimizationSDP.objFun {m n : ℕ} (_p : TraceMinimizationSDP m n)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Matrix.trace X

theorem trace_Bt_Ainv_B_jointlyConvex :
    JointlyConvex
      {A : Matrix (Fin m) (Fin m) ℝ | A.PosDef}
      (Set.univ : Set (Matrix (Fin m) (Fin n) ℝ))
      (fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ =>
        ((Matrix.trace (p.2ᵀ * p.1⁻¹ * p.2) : ℝ) : EReal)) := by
  sorry

end «CAM-Bench-712»
