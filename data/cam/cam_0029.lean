import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-29»

theorem omega_convex_of_linear_eq_and_convex_ineq
    {n : ℕ} {E 𝓘 : Type*}
    (c : (E ⊕ 𝓘) → (Fin n → ℝ) → ℝ)
    (Ω : Set (Fin n → ℝ))
    (hΩ :
      Ω =
        {x | (∀ i : E, c (Sum.inl i) x = 0) ∧
          ∀ i : 𝓘, 0 ≤ c (Sum.inr i) x})
    (hlin : ∀ i : E, IsLinearMap ℝ (c (Sum.inl i)))
    (hconc : ∀ i : 𝓘, ConvexOn ℝ Set.univ (fun x => -c (Sum.inr i) x)) :
    Convex ℝ Ω := by
  sorry

end «CAM-Bench-29»
