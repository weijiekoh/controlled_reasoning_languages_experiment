import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-776»

def proximalOperator {n : ℕ} (φ : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {u | IsMinOn (fun v : Fin n → ℝ => φ v + ((1 : EReal) / 2) * (((‖v - x‖ : ℝ) ^ 2 : ℝ) : EReal)) Set.univ u}

theorem proximalOperator_prod_eq
    {m n : ℕ}
    (φ₁ : (Fin m → ℝ) → EReal)
    (φ₂ : (Fin n → ℝ) → EReal)
    (x : Fin m → ℝ)
    (y : Fin n → ℝ) :
    let h : (Fin (m + n) → ℝ) → EReal :=
      fun z => φ₁ (fun i : Fin m => z (Fin.castAdd n i)) + φ₂ (fun j : Fin n => z (Fin.natAdd m j))
    proximalOperator h (Fin.append x y) =
      {z : Fin (m + n) → ℝ | (fun i : Fin m => z (Fin.castAdd n i)) ∈ proximalOperator φ₁ x ∧
           (fun j : Fin n => z (Fin.natAdd m j)) ∈ proximalOperator φ₂ y} := by
  sorry

end «CAM-Bench-776»
