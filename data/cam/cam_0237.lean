import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-237»

theorem sum_exp_neg_inv_convexOn
    {n m : ℕ} (f : Fin m → (EuclideanSpace ℝ (Fin n) → ℝ))
    (hconv : ∀ i : Fin m, ConvexOn ℝ {x : EuclideanSpace ℝ (Fin n) | f i x < 0} (f i))
    (hneg_conv :
      ∀ i : Fin m,
        ConvexOn ℝ {x : EuclideanSpace ℝ (Fin n) | f i x < 0}
          (fun x => Real.exp (-((f i x)⁻¹))))
    :
    ConvexOn ℝ
      {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin m, f i x < 0}
      (fun x => ∑ i : Fin m, Real.exp (-((f i x)⁻¹))) := by
  sorry

end «CAM-Bench-237»
