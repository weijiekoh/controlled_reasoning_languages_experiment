import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-314»

def infimalConvolution {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x => sInf {r : EReal | ∃ y : Fin n → ℝ, r = f₁ y + f₂ (x - y)}

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun z => sSup {r : EReal | ∃ x : Fin n → ℝ, r = (∑ i, (z i) * (x i)) - f x}

theorem convexConjugate_infimalConvolution_quadratic
    {n : ℕ}
    (hn : 0 < n)
    (f₁ f₂ : (Fin n → ℝ) → EReal)
    (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ)
    (hP₁_symm : P₁.IsSymm)
    (hP₂_symm : P₂.IsSymm)
    (hP₁_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i, x i * ∑ j, P₁ i j * x j)
    (hP₂_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < ∑ i, x i * ∑ j, P₂ i j * x j)
    (hf₁ : f₁ = fun x => ((1 : EReal) / 2) * (∑ i, x i * ∑ j, P₁ i j * x j))
    (hf₂ : f₂ = fun x => ((1 : EReal) / 2) * (∑ i, x i * ∑ j, P₂ i j * x j)) :
    convexConjugate (infimalConvolution f₁ f₂) =
      fun z => convexConjugate f₁ z + convexConjugate f₂ z := by
  sorry

end «CAM-Bench-314»
