import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-483»

theorem variance_larger_does_not_imply_larger_convex_expectation :
    ConvexOn ℝ Set.univ (fun x : ℝ => if x ≤ 0 then 0 else x) ∧
    ((1 : ℝ) / 10 * (4 : ℝ) + (9 : ℝ) / 10 * (-(4 : ℝ) / 9) = 0) ∧
    ((1 : ℝ) / 2 * (1 : ℝ) + (1 : ℝ) / 2 * (-1 : ℝ) = 0) ∧
    ((1 : ℝ) / 10 * (4 : ℝ)^2 + (9 : ℝ) / 10 * (-(4 : ℝ) / 9)^2 -
      (((1 : ℝ) / 10 * (4 : ℝ) + (9 : ℝ) / 10 * (-(4 : ℝ) / 9))^2) = (16 : ℝ) / 9) ∧
    ((16 : ℝ) / 9 > 1) ∧
    ((1 : ℝ) / 2 * (1 : ℝ)^2 + (1 : ℝ) / 2 * (-1 : ℝ)^2 -
      (((1 : ℝ) / 2 * (1 : ℝ) + (1 : ℝ) / 2 * (-1 : ℝ))^2) = 1) ∧
    ((1 : ℝ) / 10 * (if (0 : ℝ) + (4 : ℝ) ≤ 0 then 0 else (0 : ℝ) + (4 : ℝ)) +
      (9 : ℝ) / 10 * (if (0 : ℝ) + (-(4 : ℝ) / 9) ≤ 0 then 0 else (0 : ℝ) + (-(4 : ℝ) / 9)) = (2 : ℝ) / 5) ∧
    ((1 : ℝ) / 10 * (if (4 : ℝ) ≤ 0 then 0 else (4 : ℝ)) +
      (9 : ℝ) / 10 * (if (-(4 : ℝ) / 9) ≤ 0 then 0 else (-(4 : ℝ) / 9)) = (2 : ℝ) / 5) ∧
    ((2 : ℝ) / 5 < (1 : ℝ) / 2) ∧
    ((1 : ℝ) / 2 * (if (1 : ℝ) ≤ 0 then 0 else (1 : ℝ)) +
      (1 : ℝ) / 2 * (if (-1 : ℝ) ≤ 0 then 0 else (-1 : ℝ)) = (1 : ℝ) / 2) ∧
    ((1 : ℝ) / 2 * (if (0 : ℝ) + (1 : ℝ) ≤ 0 then 0 else (0 : ℝ) + (1 : ℝ)) +
      (1 : ℝ) / 2 * (if (0 : ℝ) + (-1 : ℝ) ≤ 0 then 0 else (0 : ℝ) + (-1 : ℝ)) = (1 : ℝ) / 2) := by
  sorry

end «CAM-Bench-483»
