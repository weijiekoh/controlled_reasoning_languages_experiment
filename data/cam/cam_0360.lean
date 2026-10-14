import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-360»

def bregmanDivergence {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (_grad_f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ := by
  classical
  by_cases hxy : x ∈ C ∧ y ∈ C
  · exact f x - f y - ⟪gradient f y, x - y⟫
  · exact 0

open scoped RealInnerProductSpace

theorem bregmanDivergence_eq_sum_xlog_ratio_sub_add {n : ℕ}
    (hn : 1 ≤ n)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ i : Fin n, 0 < x i)
    (hy : ∀ i : Fin n, 0 < y i) :
    bregmanDivergence
      {z : EuclideanSpace ℝ (Fin n) | ∀ i : Fin n, 0 < z i}
      (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i))
      (gradient (fun z : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n, z i * Real.log (z i)))
      x y =
      ∑ i : Fin n, (x i * Real.log (x i / y i) - x i + y i) := by
  sorry

end «CAM-Bench-360»
