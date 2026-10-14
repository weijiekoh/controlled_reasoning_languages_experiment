import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-632»

structure LinearProgram where
  n : ℕ
  mIneq : ℕ
  mEq : ℕ
  c : Fin n → ℝ
  AIneq : Fin mIneq → Fin n → ℝ
  bIneq : Fin mIneq → ℝ
  AEq : Fin mEq → Fin n → ℝ
  bEq : Fin mEq → ℝ

def NonsingularMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Ainv : Matrix (Fin n) (Fin n) ℝ,
    A * Ainv = 1 ∧ Ainv * A = 1

def optimalValue {α : Type*} (S : Set α) (f : α → EReal) : EReal :=
  sInf (f '' S)

def LinearProgramIneqNonsing
    (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ)
    (_hA : NonsingularMatrix A) : EReal :=
  optimalValue
    {x : Fin n → ℝ | ∀ i : Fin n, (∑ j : Fin n, (A i j) * (x j)) ≤ b i}
    (fun x : Fin n → ℝ => (((∑ i : Fin n, (c i) * (x i)) : ℝ) : EReal))

open Matrix
attribute [local instance] Classical.propDecidable

theorem LinearProgramIneqNonsing.pStar_eq_cMul_Ainv_b_iff_ATinv_c_nonpos
    (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (b c : Fin n → ℝ)
    (hA : NonsingularMatrix A) :
    let Ainv : Matrix (Fin n) (Fin n) ℝ := Classical.choose hA
    LinearProgramIneqNonsing n A b c hA =
      if ∀ i : Fin n, (∑ j : Fin n, Ainv.transpose i j * c j) ≤ 0
      then
        (((∑ i : Fin n, c i * (∑ j : Fin n, Ainv i j * b j)) : ℝ) : EReal)
      else
        (⊥ : EReal) := by
  sorry

end «CAM-Bench-632»
