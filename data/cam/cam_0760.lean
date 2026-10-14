import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-760»

theorem constant_stepsize_suboptimality_bound
    {n k : ℕ} (hk : 0 < k) (x0 xStar : EuclideanSpace ℝ (Fin n)) (fHatk fStar G t : ℝ)
    (hG : 0 < G) (ht : 0 < t)
    (hest :
      fHatk - fStar ≤
        (‖x0 - xStar‖ ^ 2 + G ^ 2 * (∑ i ∈ Finset.range k, t ^ 2)) /
          (2 * (∑ i ∈ Finset.range k, t))) :
    fHatk - fStar ≤ ‖x0 - xStar‖ ^ 2 / (2 * (k : ℝ) * t) + G ^ 2 * t / 2 := by
  sorry

end «CAM-Bench-760»
