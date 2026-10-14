import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-331»

def IsGaussianRandomVector {n : ℕ} (X : Fin n → ℝ → ℝ) : Prop :=
  ∃ μ : Fin n → ℝ,
    ∃ Sigma : Matrix (Fin n) (Fin n) ℝ,
      Sigma.IsSymm ∧
      Sigma.PosSemidef ∧
      ∀ a : Fin n → ℝ,
        ∃ Z : ℝ → ℝ,
          Z = (fun t => ∑ i, a i * X i t) ∧
          ∃ m : ℝ,
            ∃ v : ℝ,
              m = dotProduct a μ ∧
              v = dotProduct a (Sigma.mulVec a)

def matrixEntrywiseL1Norm {p q : Type} [Fintype p] [Fintype q] (M : Matrix p q ℝ) : ℝ :=
  ∑ i, ∑ j, |M i j|

structure sparsePlausibleSystemBound
    {n m T : ℕ}
    (x : Fin T → Fin n → ℝ)
    (u : Fin T → Fin m → ℝ)
    (WsqrtInv : Matrix (Fin n) (Fin n) ℝ) where
  Ahat : Matrix (Fin n) (Fin n) ℝ
  Bhat : Matrix (Fin n) (Fin m) ℝ

def sparsePlausibleSystemResidualVector
    {n m T : ℕ}
    (x : Fin T → Fin n → ℝ)
    (u : Fin T → Fin m → ℝ)
    (WsqrtInv : Matrix (Fin n) (Fin n) ℝ)
    (Ahat : Matrix (Fin n) (Fin n) ℝ)
    (Bhat : Matrix (Fin n) (Fin m) ℝ)
    (t : Fin (T - 1)) : Fin n → ℝ :=
  let t_curr : Fin T := Fin.castLE (Nat.sub_le T 1) t
  let t_next : Fin T := ⟨t.1 + 1, by omega⟩
  Matrix.mulVec WsqrtInv
    (fun i =>
      x t_next i - Matrix.mulVec Ahat (x t_curr) i -
        Matrix.mulVec Bhat (u t_curr) i)

def sparsePlausibleSystemResidualEnergy
    {n m T : ℕ}
    (x : Fin T → Fin n → ℝ)
    (u : Fin T → Fin m → ℝ)
    (WsqrtInv : Matrix (Fin n) (Fin n) ℝ)
    (Ahat : Matrix (Fin n) (Fin n) ℝ)
    (Bhat : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ t : Fin (T - 1),
    let r := sparsePlausibleSystemResidualVector x u WsqrtInv Ahat Bhat t
    dotProduct r r

def sparsePlausibleSystemFeasible
    {n m T : ℕ}
    (x : Fin T → Fin n → ℝ)
    (u : Fin T → Fin m → ℝ)
    (WsqrtInv : Matrix (Fin n) (Fin n) ℝ)
    (Ahat : Matrix (Fin n) (Fin n) ℝ)
    (Bhat : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  sparsePlausibleSystemResidualEnergy x u WsqrtInv Ahat Bhat ≤
    n * (T - 1) + 2 * Real.sqrt (2 * n * (T - 1))

structure SparsePlausibleSystemResidual
    (n m T : ℕ) where
  x : Fin T → Fin n → ℝ
  u : Fin T → Fin m → ℝ
  WsqrtInv : Matrix (Fin n) (Fin n) ℝ
  Ahat : Matrix (Fin n) (Fin n) ℝ
  Bhat : Matrix (Fin n) (Fin m) ℝ

def SparsePlausibleSystemResidual.objective
    {n m T : ℕ} (P : SparsePlausibleSystemResidual n m T) : ℝ :=
  matrixEntrywiseL1Norm P.Ahat + matrixEntrywiseL1Norm P.Bhat

structure SparsePlausibleSystemIdentification (n m T : ℕ) where
  x : Fin T → Fin n → ℝ
  u : Fin T → Fin m → ℝ
  WsqrtInv : Matrix (Fin n) (Fin n) ℝ
  Ahat : Matrix (Fin n) (Fin n) ℝ
  Bhat : Matrix (Fin n) (Fin m) ℝ

def SparsePlausibleSystemIdentification.objective
    {n m T : ℕ} (P : SparsePlausibleSystemIdentification n m T) : ℝ :=
  matrixEntrywiseL1Norm P.Ahat + matrixEntrywiseL1Norm P.Bhat

def SparsePlausibleSystemIdentification.is_feasible
    {n m T : ℕ} (P : SparsePlausibleSystemIdentification n m T) : Prop :=
  sparsePlausibleSystemFeasible P.x P.u P.WsqrtInv P.Ahat P.Bhat

def SparsePlausibleSystemIdentification.isOptimal
    {n m T : ℕ} (P : SparsePlausibleSystemIdentification n m T) : Prop :=
  IsLeast
    {v : ℝ | ∃ A' : Matrix (Fin n) (Fin n) ℝ, ∃ B' : Matrix (Fin n) (Fin m) ℝ,
      sparsePlausibleSystemFeasible P.x P.u P.WsqrtInv A' B' ∧
        v = matrixEntrywiseL1Norm A' + matrixEntrywiseL1Norm B'}
    P.objective

theorem sparse_plausible_system_identification_feasible_set_convex
    {n m T : ℕ} (hT : 2 ≤ T)
    (x : Fin T → Fin n → ℝ)
    (u : Fin T → Fin m → ℝ)
    (WsqrtInv : Matrix (Fin n) (Fin n) ℝ) :
    Convex ℝ
      {AB : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin m) ℝ |
        sparsePlausibleSystemFeasible x u WsqrtInv AB.1 AB.2} ∧
    ConvexOn ℝ
      {AB : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin m) ℝ |
        sparsePlausibleSystemFeasible x u WsqrtInv AB.1 AB.2}
      (fun AB => matrixEntrywiseL1Norm AB.1 + matrixEntrywiseL1Norm AB.2) := by
  sorry

end «CAM-Bench-331»
