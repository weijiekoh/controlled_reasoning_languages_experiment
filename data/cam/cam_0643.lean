import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-643»

theorem pz_plus_q_not_componentwise_nonnegative
    (P : Matrix (Fin 3) (Fin 3) ℝ)
    (q l u z : Fin 3 → ℝ)
    (hP_nonpos : ∀ i j, P i j ≤ 0)
    (hl : ∀ i, l i ≤ z i)
    (hu : ∀ i, z i ≤ u i)
    (hPlq_nonneg : ∀ i, 0 ≤ (P.mulVec l) i + q i)
    (hPuq_nonneg : ∀ i, 0 ≤ (P.mulVec u) i + q i)
    (hz : z = ![1, -1, 1])
    (hval : P.mulVec z + q = ![-0.9, 31, 9]) :
    ¬ (∀ i, 0 ≤ (P.mulVec z) i + q i) := by
  sorry

end «CAM-Bench-643»
