import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-492»

theorem isoelasticUtility_concave_monotone_and_at_one
    :
    ∀ α : ℝ, (α = 0 ∨ (0 < α ∧ α ≤ 1)) →
      ConcaveOn ℝ (Set.Ioi (0 : ℝ))
        (fun y : ℝ => if α = 0 then Real.log y else (y ^ α - 1) / α) ∧
      MonotoneOn
        (fun y : ℝ => if α = 0 then Real.log y else (y ^ α - 1) / α)
        (Set.Ioi (0 : ℝ)) ∧
      (if α = 0 then Real.log 1 else ((1 : ℝ) ^ α - 1) / α) = 0 := by
  sorry

end «CAM-Bench-492»
