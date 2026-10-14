import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-228»

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup (Set.range fun x : Fin n → ℝ => (∑ i, y i * x i : ℝ) - f x)

theorem cshub_convex_and_convexConjugate_eq
    {n : ℕ}
    (f_hub : ℝ → ℝ)
    (f_cshub : (Fin n → ℝ) → ℝ)
    (hf_hub :
      ∀ t : ℝ,
        f_hub t =
          if |t| ≤ 1 then
            (1 / 2 : ℝ) * t ^ 2
          else
            |t| - (1 / 2 : ℝ))
    (hf_cshub :
      ∀ x : Fin n → ℝ,
        f_cshub x =
          f_hub (Real.sqrt (∑ i, (x i) ^ 2))) :
    ConvexOn ℝ Set.univ f_cshub ∧
      ∀ y : Fin n → ℝ,
        convexConjugate (fun x => (f_cshub x : EReal)) y =
          if Real.sqrt (∑ i, (y i) ^ 2) ≤ 1 then
            ((1 / 2 : ℝ) * (∑ i, (y i) ^ 2) : EReal)
          else
            ⊤ := by
  sorry

end «CAM-Bench-228»
