import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-233»

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r : EReal | ∃ x : Fin n → ℝ, r = ∑ i, y i * x i - f x}

def infimalConvolution {m n : ℕ} (f : Fin m → (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x =>
    sInf {r : EReal | ∃ xs : Fin m → (Fin n → ℝ), (∀ i, f i (xs i) ≠ ⊤) ∧ (∑ i, xs i = x) ∧ r = ∑ i, f i (xs i)}

theorem convexConjugate_infimalConvolution_eq_sum_convexConjugate {m n : ℕ}
    (f : Fin m → (Fin n → ℝ) → EReal) :
    convexConjugate (infimalConvolution f) = fun y => ∑ i, convexConjugate (f i) y := by
  sorry

end «CAM-Bench-233»
