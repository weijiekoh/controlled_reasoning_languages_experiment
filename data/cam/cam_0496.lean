import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-496»

theorem ratio_pos_quasiconvex_quasiconcave_not_convex_not_concave :
    let Rpp2 : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < x.2}
    let ratioOnRpp2 : (ℝ × ℝ) → ℝ := fun x => x.1 / x.2
    (∀ α : ℝ, Convex ℝ {x | x ∈ Rpp2 ∧ ratioOnRpp2 x ≤ α}) ∧
    (∀ α : ℝ, Convex ℝ {x | x ∈ Rpp2 ∧ α ≤ ratioOnRpp2 x}) ∧
    ¬ ConvexOn ℝ Rpp2 ratioOnRpp2 ∧
    ¬ ConcaveOn ℝ Rpp2 ratioOnRpp2 := by
  sorry

end «CAM-Bench-496»
