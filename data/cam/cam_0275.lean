import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-275»

open Matrix

structure SemidefiniteProgram (p m : ℕ) where
  c : Fin p → ℝ
  F0 : Matrix (Fin m) (Fin m) ℝ
  F : Fin p → Matrix (Fin m) (Fin m) ℝ
  F0_symm : F0.IsSymm
  F_symm : ∀ j, (F j).IsSymm

def SemidefiniteProgram.objective {p m : ℕ} (P : SemidefiniteProgram p m) (z : Fin p → ℝ) : ℝ :=
  ∑ j, P.c j * z j

def SemidefiniteProgram.lmiMatrix {p m : ℕ} (P : SemidefiniteProgram p m) (z : Fin p → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  P.F0 + ∑ j, z j • P.F j

structure LinearMatrixInequality (p m : ℕ) where
  F0 : Matrix (Fin m) (Fin m) ℝ
  F : Fin p → Matrix (Fin m) (Fin m) ℝ
  F0_symm : F0.IsSymm
  F_symm : ∀ j, (F j).IsSymm

def LinearMatrixInequality.matrix {p m : ℕ} (L : LinearMatrixInequality p m) (z : Fin p → ℝ) :
    Prop :=
  PosSemidef (L.F0 + ∑ j, z j • L.F j)

def schurComplement {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (_hA_pos : PosDef A)
    (_hM_symm : (fromBlocks A B Bᵀ C).IsSymm) :
    Matrix (Fin n) (Fin n) ℝ :=
  C - Bᵀ * A⁻¹ * B

structure MaxQuadraticFormMinimization (n m K : ℕ) where
  F0 : Matrix (Fin m) (Fin m) ℝ
  F : Fin n → Matrix (Fin m) (Fin m) ℝ
  c : Fin K → Fin m → ℝ
  F0_symm : F0.IsSymm
  F_symm : ∀ j, (F j).IsSymm
  K_pos : 1 ≤ K

def MaxQuadraticFormMinimization.matrix (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  P.F0 + ∑ j, x j • P.F j

def MaxQuadraticFormMinimization.objective (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) : ℝ :=
  let i0 : Fin K := ⟨0, Nat.succ_le_iff.mp P.K_pos⟩
  Finset.fold max
    (dotProduct (P.c i0) ((P.matrix x)⁻¹.mulVec (P.c i0)))
    (fun i => dotProduct (P.c i) ((P.matrix x)⁻¹.mulVec (P.c i)))
    Finset.univ

def MaxQuadraticFormMinimization.feasible (P : MaxQuadraticFormMinimization n m K)
    (x : Fin n → ℝ) : Prop :=
  Matrix.PosDef (P.matrix x)

theorem maxQuadraticFormMinimization_equiv_semidefinite_program
    {n m K : ℕ} (P : MaxQuadraticFormMinimization n m K) :
    ∃ (sdpFeasible : (Fin n → ℝ) → ℝ → Prop),
      (∀ (x : Fin n → ℝ) (t : ℝ),
        sdpFeasible x t ↔
          ∀ i : Fin K,
            PosSemidef
              (fromBlocks
                (P.matrix x)
                (fun a : Fin m => fun _ : Fin 1 => P.c i a)
                (fun _ : Fin 1 => fun b : Fin m => P.c i b)
                (fun _ _ : Fin 1 => t))) ∧
      (∀ (x : Fin n → ℝ),
        P.feasible x →
          P.objective x =
            sInf {t : ℝ | sdpFeasible x t}) := by
  sorry

end «CAM-Bench-275»
