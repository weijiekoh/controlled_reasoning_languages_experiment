import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-644»

open scoped BigOperators

theorem normSq_le_sum_phi_le_c_mul_normSq
    {m : ℕ} (a : ℝ) (ha : 0 < a)
    (φ : ℝ → EReal)
    (hφ : φ = fun t =>
      if |t| < a then ((-(a ^ 2)) * Real.log (1 - (t / a) ^ 2) : EReal) else (⊤ : EReal))
    (c : Set.Ici (0 : ℝ) → ℝ)
    (hc : c = fun r : Set.Ici (0 : ℝ) =>
      if hr : (r : ℝ) = 0 then 1 else ((-(a ^ 2)) * Real.log (1 - ((r : ℝ) / a) ^ 2)) / ((r : ℝ) ^ 2))
    (u : Fin m → ℝ)
    (hu : (↑(Finset.univ.sup fun i : Fin m => ‖u i‖₊) : ℝ) < a) :
    ((∑ i, (u i) ^ 2 : ℝ) : EReal) ≤ ∑ i, φ (u i) ∧
      (∑ i, φ (u i)) ≤
        ((c ⟨(↑(Finset.univ.sup fun i : Fin m => ‖u i‖₊) : ℝ), NNReal.coe_nonneg _⟩ *
            (∑ i, (u i) ^ 2 : ℝ) : ℝ) : EReal) := by
  sorry

end «CAM-Bench-644»
