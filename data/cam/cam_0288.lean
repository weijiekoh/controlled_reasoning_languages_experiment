import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-288»

def uniformDensityOnMeasurableSet {p : ℕ} (U : Set (Fin p → ℝ))
    (_hU : MeasurableSet U) (_hpos : 0 < MeasureTheory.volume U)
    (_hfin : MeasureTheory.volume U < (⊤ : ENNReal)) :
    (Fin p → ℝ) → ℝ :=
  fun x => Set.indicator U (fun _ => ((MeasureTheory.volume U).toReal)⁻¹) x

def affinePolicy {p n : ℕ} (x₀ : Fin n → ℝ) (K : Matrix (Fin n) (Fin p) ℝ) :
    (Fin p → ℝ) → (Fin n → ℝ) :=
  fun u => x₀ + K.mulVec u

def entrywiseAbsoluteValue {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin m) (Fin p) ℝ :=
  fun i j => |M i j|

structure AffinePolicyRobustProgram where
  n : ℕ
  p : ℕ
  m : ℕ
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b₀ : Fin m → ℝ
  B : Matrix (Fin m) (Fin p) ℝ
  x₀ : Fin n → ℝ
  K : Matrix (Fin n) (Fin p) ℝ

def AffinePolicyRobustProgram.isFeasible (P : AffinePolicyRobustProgram) : Prop :=
  ∀ u ∈ ({u : Fin P.p → ℝ | ∀ i, u i ∈ Set.Icc (-1 : ℝ) 1} : Set (Fin P.p → ℝ)),
    P.A.mulVec (affinePolicy P.x₀ P.K u) ≤ P.b₀ + P.B.mulVec u

structure ExplicitAffinePolicyLinearProgram where
  n : ℕ
  p : ℕ
  m : ℕ
  c : Fin n → ℝ
  A : Matrix (Fin m) (Fin n) ℝ
  b₀ : Fin m → ℝ
  B : Matrix (Fin m) (Fin p) ℝ
  x₀ : Fin n → ℝ
  K : Matrix (Fin n) (Fin p) ℝ

def ExplicitAffinePolicyLinearProgram.objective (P : ExplicitAffinePolicyLinearProgram) : ℝ :=
  P.c ⬝ᵥ P.x₀

def ExplicitAffinePolicyLinearProgram.constraintMatrix (P : ExplicitAffinePolicyLinearProgram) :
    Matrix (Fin P.m) (Fin P.p) ℝ :=
  entrywiseAbsoluteValue (P.A * P.K - P.B)

def ExplicitAffinePolicyLinearProgram.ones (P : ExplicitAffinePolicyLinearProgram) : Fin P.p → ℝ :=
  fun _ => 1

def ExplicitAffinePolicyLinearProgram.isFeasible (P : ExplicitAffinePolicyLinearProgram) : Prop :=
  P.A.mulVec P.x₀ + P.constraintMatrix.mulVec P.ones ≤ P.b₀

def ExplicitAffinePolicyLinearProgram.fromRobust
    (P : AffinePolicyRobustProgram) : ExplicitAffinePolicyLinearProgram :=
  { n := P.n
    p := P.p
    m := P.m
    c := P.c
    A := P.A
    b₀ := P.b₀
    B := P.B
    x₀ := P.x₀
    K := P.K }

theorem affinePolicyRobustProgram_equivalent_to_explicitLinearProgram
    (P : AffinePolicyRobustProgram) :
    P.isFeasible ↔ (ExplicitAffinePolicyLinearProgram.fromRobust P).isFeasible := by
  sorry

end «CAM-Bench-288»
