import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-206»

open Matrix

def weightedLaplacian {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A * Matrix.diagonal w * Aᵀ

structure SemidefiniteProgram (p n : ℕ) where
  F0 : Matrix (Fin n) (Fin n) ℝ
  F : Fin p → Matrix (Fin n) (Fin n) ℝ
  objective : (Fin p → ℝ) → ℝ
  eqConstraints : List ((Fin p → ℝ) → Prop)
  leConstraints : List ((Fin p → ℝ) → Prop)

def SemidefiniteProgram.HasLinearObjective {p n : ℕ} (S : SemidefiniteProgram p n) : Prop :=
  ∃ c : Fin p → ℝ, S.objective = fun x => ∑ i, c i * x i

def SemidefiniteProgram.HasAffineConstraints {p n : ℕ} (S : SemidefiniteProgram p n) : Prop :=
  (∀ g ∈ S.eqConstraints, ∃ A : Fin p → ℝ, ∃ b : ℝ, g = fun x => (∑ i, A i * x i) = b) ∧
    (∀ g ∈ S.leConstraints, ∃ A : Fin p → ℝ, ∃ b : ℝ, g = fun x => (∑ i, A i * x i) ≤ b)

def SemidefiniteProgram.matrixExpr {p n : ℕ} (S : SemidefiniteProgram p n) (x : Fin p → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.F0 + ∑ i, x i • S.F i

def SemidefiniteProgram.isFeasible {p n : ℕ} (S : SemidefiniteProgram p n) (x : Fin p → ℝ) :
    Prop :=
  (∀ v : Fin n → ℝ, 0 ≤ dotProduct v ((S.matrixExpr x).mulVec v)) ∧
    (∀ g ∈ S.eqConstraints, g x) ∧
    (∀ g ∈ S.leConstraints, g x)

structure AlgebraicConnectivityMaximization (m p n : ℕ) where
  F : Matrix (Fin p) (Fin m) ℝ
  g : Fin p → ℝ

def spectralThresholdMatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (w : Fin m → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  weightedLaplacian A w -
    t • ((1 : Matrix (Fin n) (Fin n) ℝ) -
      (1 / (n : ℝ)) • fun _ _ => (1 : ℝ))

def AlgebraicConnectivityMaximization.sdpConstraint
    {m p n : ℕ} (_P : AlgebraicConnectivityMaximization m p n)
    (A : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) (t : ℝ) : Prop :=
  Matrix.PosSemidef (spectralThresholdMatrix A w t)

def AlgebraicConnectivityMaximization.lambda2
    {m p n : ℕ} (P : AlgebraicConnectivityMaximization m p n)
    (A : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) : ℝ :=
  sSup {t : ℝ | P.sdpConstraint A w t}

def AlgebraicConnectivityMaximization.objective
    {m p n : ℕ} (P : AlgebraicConnectivityMaximization m p n)
    (A : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) : ℝ :=
  P.lambda2 A w

def AlgebraicConnectivityMaximization.isFeasible
    {m p n : ℕ} (P : AlgebraicConnectivityMaximization m p n) (w : Fin m → ℝ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ ∀ i, (∑ j, P.F i j * w j) ≤ P.g i

theorem algebraicConnectivityMaximization_sdp_supremum_characterization
    {m p n : ℕ} (_hn : 2 ≤ n) (A : Matrix (Fin n) (Fin m) ℝ) (P : AlgebraicConnectivityMaximization m p n)
    (hgraph :
      ∀ k : Fin m,
        ∃ i j : Fin n,
          i ≠ j ∧
          A i k = 1 ∧
          A j k = -1 ∧
          ∀ ℓ : Fin n, ℓ ≠ i → ℓ ≠ j → A ℓ k = 0)
    (hsdp_nonempty :
      ∀ w : Fin m → ℝ, P.isFeasible w → {t : ℝ | P.sdpConstraint A w t}.Nonempty)
    (hsdp_bdd :
      ∀ w : Fin m → ℝ, P.isFeasible w → BddAbove {t : ℝ | P.sdpConstraint A w t}) :
    ∀ w : Fin m → ℝ, P.isFeasible w →
      ∀ t : ℝ,
        P.sdpConstraint A w t →
          t ≤ P.lambda2 A w ∧
          ∀ u : ℝ, (∀ τ : ℝ, P.sdpConstraint A w τ → τ ≤ u) → P.lambda2 A w ≤ u := by
  sorry

end «CAM-Bench-206»
