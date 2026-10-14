import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-724»

open scoped BigOperators

theorem lp_quasinorm_concave_on_positive_orthant
    {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ConcaveOn ℝ {x : Fin n → ℝ | ∀ i, 0 < x i}
      (fun x => (∑ i, (x i) ^ p) ^ (1 / p)) := by
  sorry

end «CAM-Bench-724»
