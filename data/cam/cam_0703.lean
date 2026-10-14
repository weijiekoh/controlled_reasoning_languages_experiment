import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-703»

def euclideanLength {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

theorem ratio_squaredNorm_affine_denominator_isClosedFunction
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hA : Module.finrank ℝ (LinearMap.range A.toLin') = n)
    (hb : b ∉ Set.range fun y : Fin n → ℝ => A.mulVec y) :
    let f : (Fin n → ℝ) → EReal :=
      fun x =>
        if 0 < dotProduct c x + d then
          (((euclideanLength (A.mulVec x - b) ^ 2 : ℝ) / (dotProduct c x + d)) : EReal)
        else
          ⊤
    IsClosed {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  sorry

end «CAM-Bench-703»
