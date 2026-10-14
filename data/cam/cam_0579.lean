import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-579»

open scoped BigOperators
theorem convexOn_iff_convex_and_hessian_posSemidef
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (_hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ z : Fin n → ℝ,
        0 ≤
          ∑ i : Fin n, z i *
            ∑ j : Fin n,
              z j *
                ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
                  (Pi.single i (1 : ℝ))) := by
  sorry

end «CAM-Bench-579»
