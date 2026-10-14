import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-276»

structure SemidefiniteProgram (n p : ℕ) where
  A : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ
  c : Fin p → ℝ
  d : ℝ

def SemidefiniteProgram.lmi {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.A 0 + ∑ i : Fin p, z i • S.A i.succ

def SemidefiniteProgram.objective {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) : ℝ :=
  ∑ i : Fin p, S.c i * z i + S.d

def SemidefiniteProgram.IsFeasible {n p : ℕ} (S : SemidefiniteProgram n p) (z : Fin p → ℝ) :
    Prop :=
  Matrix.PosSemidef (S.lmi z)

structure SchurComplementSemidefiniteProgram (m n : ℕ) where
  F : (Fin n → ℝ) → Matrix (Fin m) (Fin m) ℝ

def SchurComplementSemidefiniteProgram.blockMatrix {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (P.F x) 1 1 (t • (1 : Matrix (Fin m) (Fin m) ℝ))

def SchurComplementSemidefiniteProgram.isFeasible {m n : ℕ}
    (P : SchurComplementSemidefiniteProgram m n) (x : Fin n → ℝ) (t : ℝ) : Prop :=
  Matrix.PosDef (P.F x) ∧ Matrix.PosSemidef (P.blockMatrix x t)

theorem schurComplement_equivalent_to_unit_ball_quadratic_form_minimization
    (m n : ℕ)
    (F : Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ)
    (hFsymm : ∀ i : Fin (n + 1), (F i).IsSymm) :
    let P : SchurComplementSemidefiniteProgram m n :=
      { F := fun x => F 0 + ∑ i : Fin n, x i • F i.succ }
    sInf
        {r : ℝ | ∃ x : Fin n → ℝ,
          Matrix.PosDef (P.F x) ∧
          sSup {q : ℝ | ∃ c : Fin m → ℝ, ‖c‖ ≤ 1 ∧
            c ⬝ᵥ ((P.F x)⁻¹).mulVec c = q} = r} =
      sInf
        {t : ℝ | ∃ x : Fin n → ℝ,
          P.isFeasible x t} := by
  sorry

end «CAM-Bench-276»
