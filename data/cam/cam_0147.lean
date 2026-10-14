import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-147»

theorem quadratic_model_interpolation_conditions_count
    (n : ℕ) :
    1 + n + n * (n + 1) / 2 = (n + 1) * (n + 2) / 2 := by
  sorry

end «CAM-Bench-147»
