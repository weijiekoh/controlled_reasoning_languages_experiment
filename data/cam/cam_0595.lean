import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-595»

theorem infimum_and_minimizer_of_Exercise_4_1_a :
    sInf {r : ℝ | ∃ x : Fin 2 → ℝ,
      0 ≤ x 0 ∧
      0 ≤ x 1 ∧
      1 ≤ 2 * x 0 + x 1 ∧
      1 ≤ x 0 + 3 * x 1 ∧
      r = x 0 + x 1} = (3 : ℝ) / 5 ∧
    {x : Fin 2 → ℝ |
      0 ≤ x 0 ∧
      0 ≤ x 1 ∧
      1 ≤ 2 * x 0 + x 1 ∧
      1 ≤ x 0 + 3 * x 1 ∧
      x 0 + x 1 = (3 : ℝ) / 5} =
      {x : Fin 2 → ℝ | x = ![(2 : ℝ) / 5, (1 : ℝ) / 5]} := by
  sorry

end «CAM-Bench-595»
