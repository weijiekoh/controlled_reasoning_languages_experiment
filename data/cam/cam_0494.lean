import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-494»

theorem mul_pos_neither_convex_nor_concave_not_quasiconvex_but_quasiconcave :
    ¬ ConvexOn ℝ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} (fun p => p.1 * p.2) ∧
    ¬ ConcaveOn ℝ {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} (fun p => p.1 * p.2) ∧
    ¬ Convex ℝ {q : (ℝ × ℝ) × ℝ | (0 < q.1.1 ∧ 0 < q.1.2) ∧ q.1.1 * q.1.2 ≤ q.2} ∧
    ∀ α : ℝ, Convex ℝ {p : ℝ × ℝ | (0 < p.1 ∧ 0 < p.2) ∧ α ≤ p.1 * p.2} := by
  sorry

end «CAM-Bench-494»
