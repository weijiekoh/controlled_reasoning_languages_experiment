import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-12»

def feasibleDirectionSet (Ω : Set (Fin n → ℝ)) (xStar : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {d | ∃ tBar > 0, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) tBar → xStar + t • d ∈ Ω}

theorem tangentCone_and_feasibleDirectionSet_at_origin_for_parabolic_region :
    let Ω : Set (Fin 2 → ℝ) :=
      {x | 0 ≤ x 1 ∧ x 1 ≤ (x 0)^2}
    let xStar : Fin 2 → ℝ := fun _ => 0
    ({d : Fin 2 → ℝ |
        ∃ t : ℕ → ℝ, (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝[>] (0 : ℝ)) ∧
        ∃ x : ℕ → (Fin 2 → ℝ), (∀ k, x k ∈ Ω) ∧ Tendsto x atTop (𝓝 xStar) ∧
          Tendsto (fun k => (1 / t k) • (x k - xStar)) atTop (𝓝 d)} =
      {d | d 1 = 0}) ∧
    feasibleDirectionSet Ω xStar = {d | d 1 = 0} := by
  sorry

end «CAM-Bench-12»
