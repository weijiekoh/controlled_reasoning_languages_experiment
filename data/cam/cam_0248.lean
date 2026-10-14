import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-248»

def loewnerOrder {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ B.IsSymm ∧ Matrix.PosSemidef (B - A)

def schurComplement {n m : ℕ} (X11 : Matrix (Fin n) (Fin n) ℝ)
    (X12 : Matrix (Fin n) (Fin m) ℝ)
    (X22 : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  X11 - X12 * X22⁻¹ * X12.transpose

structure LogDetSemidefiniteProgram where
  n : ℕ
  m : ℕ
  X11 : Matrix (Fin m) (Fin m) ℝ
  X12 : Matrix (Fin m) (Fin n) ℝ
  X22 : Matrix (Fin n) (Fin n) ℝ
  Y : Matrix (Fin m) (Fin m) ℝ

def LogDetSemidefiniteProgram.objective (p : LogDetSemidefiniteProgram) : ℝ :=
  Real.log (Matrix.det (p.Y⁻¹))

def LogDetSemidefiniteProgram.isFeasible (p : LogDetSemidefiniteProgram) : Prop :=
  p.X11.IsSymm ∧
  p.X22.IsSymm ∧
  p.Y.IsSymm ∧
  Matrix.PosDef p.Y ∧
  (Matrix.fromBlocks p.Y
    (0 : Matrix (Fin p.m) (Fin p.n) ℝ)
    (0 : Matrix (Fin p.n) (Fin p.m) ℝ)
    (0 : Matrix (Fin p.n) (Fin p.n) ℝ)).IsSymm ∧
  (Matrix.fromBlocks p.X11 p.X12 p.X12.transpose p.X22).IsSymm ∧
  Matrix.PosSemidef
    ((Matrix.fromBlocks p.X11 p.X12 p.X12.transpose p.X22) -
      Matrix.fromBlocks p.Y
        (0 : Matrix (Fin p.m) (Fin p.n) ℝ)
        (0 : Matrix (Fin p.n) (Fin p.m) ℝ)
        (0 : Matrix (Fin p.n) (Fin p.n) ℝ))

def LogDetSemidefiniteProgram.schurComplementData (p : LogDetSemidefiniteProgram) :
    Matrix (Fin p.m) (Fin p.m) ℝ :=
  schurComplement p.X11 p.X12 p.X22

theorem schur_complement_solves_logDetSemidefiniteProgram
    {n m : ℕ} (hmn : m ≤ n)
    (X11 : Matrix (Fin m) (Fin m) ℝ)
    (X12 : Matrix (Fin m) (Fin (n - m)) ℝ)
    (X22 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)
    (hX11symm : X11.IsSymm)
    (hX22symm : X22.IsSymm)
    (hXpos :
      Matrix.PosDef (Matrix.fromBlocks X11 X12 X12.transpose X22)) :
    let Yopt := schurComplement X11 X12 X22
    ((Matrix.fromBlocks Yopt
        (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
        (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
      (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
      Matrix.PosSemidef
        ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
          Matrix.fromBlocks Yopt
            (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
            (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) ∧
    Matrix.PosDef Yopt ∧
    ∀ Y : Matrix (Fin m) (Fin m) ℝ,
      Y.IsSymm →
      Matrix.PosDef Y →
      ((Matrix.fromBlocks Y
          (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
          (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ)).IsSymm ∧
        (Matrix.fromBlocks X11 X12 X12.transpose X22).IsSymm ∧
        Matrix.PosSemidef
          ((Matrix.fromBlocks X11 X12 X12.transpose X22) -
            Matrix.fromBlocks Y
              (0 : Matrix (Fin m) (Fin (n - m)) ℝ)
              (0 : Matrix (Fin (n - m)) (Fin m) ℝ)
              (0 : Matrix (Fin (n - m)) (Fin (n - m)) ℝ))) →
      Real.log (Matrix.det (Yopt⁻¹)) ≤ Real.log (Matrix.det (Y⁻¹)) := by
  sorry

end «CAM-Bench-248»
