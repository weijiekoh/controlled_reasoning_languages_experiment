import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-411»

def SelfConcordantOnRpp (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f {x : ℝ | 0 < x} ∧
  ConvexOn ℝ {x : ℝ | 0 < x} f ∧
  ∀ x : ℝ, 0 < x →
    0 ≤ deriv (fun y => deriv f y) x ∧
    |deriv (fun y => deriv (fun z => deriv f z) y) x| ≤
      2 * Real.rpow (deriv (fun y => deriv f y) x) (3 / 2 : ℝ)

theorem txLogx_sub_log_selfConcordantOnRpp {t : ℝ} (ht : 0 < t) :
    SelfConcordantOnRpp (fun x : ℝ => t * x * Real.log x - Real.log x) := by
  sorry

end «CAM-Bench-411»
