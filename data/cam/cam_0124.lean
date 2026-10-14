import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-124»

open scoped BigOperators

theorem exact_line_search_step_size_quadratic
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (b xₖ pₖ : n → ℝ) (αₖ : ℝ)
    (hpₖ : pₖ ≠ 0)
    (hAp : dotProduct pₖ (fun i => ∑ j, A i j * pₖ j) ≠ 0)
    (hmin : ∀ α : ℝ,
      (1 / 2 : ℝ) * dotProduct (fun i => xₖ i + αₖ * pₖ i) (fun i => ∑ j, A i j * (xₖ j + αₖ * pₖ j))
        - dotProduct b (fun i => xₖ i + αₖ * pₖ i)
      ≤
      (1 / 2 : ℝ) * dotProduct (fun i => xₖ i + α * pₖ i) (fun i => ∑ j, A i j * (xₖ j + α * pₖ j))
        - dotProduct b (fun i => xₖ i + α * pₖ i)) :
    αₖ = - dotProduct (fun i => ∑ j, A i j * xₖ j - b i) pₖ
      / dotProduct pₖ (fun i => ∑ j, A i j * pₖ j) := by
  sorry

end «CAM-Bench-124»
