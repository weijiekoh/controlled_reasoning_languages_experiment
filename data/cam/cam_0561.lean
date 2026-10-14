import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-561»

open scoped BigOperators

theorem prod_div_sum_logConcave_on_posOrthant
    (n : ℕ) (hn : 1 ≤ n) :
    let s : Set (Fin n → ℝ) := {x | ∀ i, 0 < x i}
    let f : (Fin n → ℝ) → ℝ := fun x => (∏ i, x i) / (∑ i, x i)
    (∀ x ∈ s, 0 < f x) ∧
      ConcaveOn ℝ s (fun x => Real.log (f x)) := by
  sorry

end «CAM-Bench-561»
