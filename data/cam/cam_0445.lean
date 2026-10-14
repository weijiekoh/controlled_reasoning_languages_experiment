import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-445»

theorem preimage_halfspace_linear_fractional
    {m n : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (b g : Fin n → ℝ)
    (c : Fin m → ℝ)
    (d h : ℝ) :
    {x : Fin m → ℝ |
        ((∑ i, g i * (((∑ j, A i j * x j) + b i) / ((∑ j, c j * x j) + d))) ≤ h) ∧
        ((∑ j, c j * x j) + d > 0)} =
      {x : Fin m → ℝ |
        ((∑ j, ((∑ i, A i j * g i) - h * c j) * x j) ≤ h * d - ∑ i, g i * b i) ∧
        ((∑ j, c j * x j) + d > 0)} := by
  sorry

end «CAM-Bench-445»
