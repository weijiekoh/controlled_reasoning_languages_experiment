import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-111»

open scoped RealInnerProductSpace

def WolfeConditions
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xk pk : EuclideanSpace ℝ (Fin n))
    (c₁ c₂ α : ℝ) : Prop :=
  0 < c₁ ∧ c₁ < c₂ ∧ c₂ < 1 ∧ 0 < α ∧
  ⟪f' xk, pk⟫ < 0 ∧
  f (xk + α • pk) ≤ f xk + c₁ * α * ⟪f' xk, pk⟫ ∧
  c₂ * ⟪f' xk, pk⟫ ≤ ⟪f' (xk + α • pk), pk⟫

theorem exists_no_step_length_satisfying_WolfeConditions_of_c₂_lt_c₁
    {n : ℕ} (hn : 0 < n) (hpos : 0 < c₂) (hc : c₂ < c₁) (hc₁ : c₁ < 1) :
    ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (xk pk : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ 1 f ∧
      (fderiv ℝ f xk) pk < 0 ∧
      ¬ ∃ α : ℝ,
        WolfeConditions f (fun x => gradient f x) xk pk c₂ c₁ α := by
  sorry

end «CAM-Bench-111»
