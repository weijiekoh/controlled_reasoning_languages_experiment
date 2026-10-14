import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-260»

def infimalConvolution {n : ℕ} (f g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x => sInf {r : EReal | ∃ y : Fin n → ℝ, r = f y + g (x - y)}

def huberPenalty {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if |x i| ≤ 1 then (x i) ^ 2 / 2 else |x i| - 1 / 2

theorem infimalConvolution_l1_sqNorm_eq_huberPenalty (n : ℕ) :
    infimalConvolution
        (fun x : Fin n → ℝ => ((∑ i, |x i| : ℝ) : EReal))
        (fun x : Fin n → ℝ => ((1 / 2 : ℝ) * ∑ i, (x i) ^ 2 : ℝ))
      =
      fun x : Fin n → ℝ => (huberPenalty x : EReal) := by
  sorry

end «CAM-Bench-260»
