import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-493»

theorem exp_sub_one_properties :
    ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp x - 1) ∧
      ¬ConcaveOn ℝ Set.univ (fun x : ℝ => Real.exp x - 1) ∧
      QuasiconvexOn ℝ Set.univ (fun x : ℝ => Real.exp x - 1) ∧
      QuasiconcaveOn ℝ Set.univ (fun x : ℝ => Real.exp x - 1) := by
  sorry

end «CAM-Bench-493»
