import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-151»

theorem quadratic_coefficients_of_interpolation_data
    {f g₁ g₂ G11sq G12 G22sq : ℝ}
    (hm1 : f = 1)
    (hm2 : f + g₁ + (1 / 2 : ℝ) * G11sq = 2.0084)
    (hm3 : f + 2 * g₁ + (1 / 2 : ℝ) * G11sq * 4 = 7.0091)
    (hm4 : f + g₁ + g₂ + (1 / 2 : ℝ) * G11sq + G12 + (1 / 2 : ℝ) * G22sq = 1.0168)
    (hm5 : f + 2 * g₂ + (1 / 2 : ℝ) * G22sq * 4 = -0.9909)
    (hm6 : f + g₂ + (1 / 2 : ℝ) * G22sq = -0.9916) :
    g₁ = -0.98775 ∧
    g₂ = -2.98775 ∧
    G11sq = 3.9923 ∧
    G12 = 1 ∧
    G22sq = 1.9923 := by
  sorry

end «CAM-Bench-151»
