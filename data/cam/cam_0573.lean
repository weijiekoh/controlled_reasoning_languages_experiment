import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-573»

theorem gamma_density_log_concave_on_Ioi
    {α lam : ℝ}
    (hlam : 1 ≤ lam)
    (hα : 0 < α) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun x =>
        Real.log
          (((α ^ lam) /
              (∫ t in Set.Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-t))) *
              x ^ (lam - 1) * Real.exp (-α * x))) := by
  sorry

end «CAM-Bench-573»
