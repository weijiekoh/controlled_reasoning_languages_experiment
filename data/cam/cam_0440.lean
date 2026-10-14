import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-440»

theorem quartile_superlevel_set_convex
    (n : ℕ) (a : Fin n.succ → ℝ) (ha : StrictMono a) (α : ℝ) :
    Convex ℝ
      {p : Fin n.succ → ℝ |
        (∑ i, p i) = 1 ∧
        (∀ i, 0 ≤ p i) ∧
        α ≤ sInf {β : ℝ | (∑ i, if a i ≤ β then p i else 0) ≥ (1 / 4 : ℝ)}} := by
  sorry

end «CAM-Bench-440»
