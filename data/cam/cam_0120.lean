import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-120»

open scoped RealInnerProductSpace

theorem norm_monotone_along_piecewise_path_to_newton_step
    {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) (g : n → ℝ)
    (hB_symm : B.IsSymm) (hB_pos : B.PosDef) (hg : g ≠ 0)
    (gamma_bar : ℝ)
    (hgamma_bar :
      gamma_bar ∈ Set.Ioc
        ((dotProduct g g) ^ 2 /
          (dotProduct g (B.mulVec g) * dotProduct g (B⁻¹.mulVec g)))
        1) :
    let pC : n → ℝ := -((dotProduct g g) / dotProduct g (B.mulVec g)) • g
    let pB : n → ℝ := -(B⁻¹.mulVec g)
    let path : ℝ → n → ℝ :=
      fun t =>
        if t ≤ (1 : ℝ) then
          t • pC
        else if t ≤ (2 : ℝ) then
          pC + (t - 1) • (gamma_bar • pB - pC)
        else
          gamma_bar • pB + (t - 2) • ((1 - gamma_bar) • pB)
    MonotoneOn (fun t => Real.sqrt (dotProduct (path t) (path t))) (Set.Icc (0 : ℝ) 3) := by
  sorry

end «CAM-Bench-120»
