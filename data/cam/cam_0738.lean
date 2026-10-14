import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-738»

open scoped BigOperators

def KarushKuhnTuckerConditions
    {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (xStar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ lam : Fin m → ℝ,
    (∀ i, 0 ≤ lam i) ∧
    (∀ i, g i xStar ≤ 0) ∧
    (∀ i, lam i * g i xStar = 0) ∧
    (gradient f xStar + ∑ i, lam i • gradient (g i) xStar = 0)

theorem exponentialConstrainedOptimizationProblem_optimal_solution_satisfies_kkt :
    let f : EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun x => Real.exp (x 0) + Real.exp (x 1)
    let g : Fin 1 → EuclideanSpace ℝ (Fin 2) → ℝ :=
      fun _ x => (x 0) ^ 2 / x 1
    ∃ xStar : EuclideanSpace ℝ (Fin 2),
      xStar 1 ≠ 0 ∧
      g 0 xStar ≤ 0 ∧
      (∀ x : EuclideanSpace ℝ (Fin 2), x 1 ≠ 0 → g 0 x ≤ 0 → f xStar ≤ f x) ∧
      KarushKuhnTuckerConditions f g xStar := by
  sorry

end «CAM-Bench-738»
