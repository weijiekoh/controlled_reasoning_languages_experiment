import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-512»

open scoped BigOperators
theorem minkowski_gauge_neg_root_convexOn
    {n : ℕ} {p q : ℝ}
    (hp : 1 < p) (hq : 1 / p + 1 / q = 1) :
    let pNormPow : (Fin n → ℝ) → ℝ :=
      fun x => ∑ i : Fin n, Real.rpow (|x i|) p
    let pNorm : (Fin n → ℝ) → ℝ :=
      fun x => Real.rpow (pNormPow x) (1 / p)
    let dom : Set ((Fin n → ℝ) × ℝ) :=
      {xt | xt.2 ≥ pNorm xt.1}
    let f : ((Fin n → ℝ) × ℝ) → ℝ :=
      fun xt => -Real.rpow (Real.rpow xt.2 p - pNormPow xt.1) (1 / p)
    ConvexOn ℝ dom f := by
  sorry

end «CAM-Bench-512»
