import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-526»

theorem convex_eq_sSup_affine_minorants_on_interior_dom
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hconv : Convex ℝ {xt : (Fin n → ℝ) × ℝ | f xt.1 ≤ (xt.2 : EReal)}) :
    let affineMinorants : Set ((Fin n → ℝ) → ℝ) :=
      {h : ((Fin n → ℝ) → ℝ) |
        (∃ a : Fin n → ℝ, ∃ b : ℝ, ∀ z : Fin n → ℝ, h z = dotProduct a z + b) ∧
        ∀ z : Fin n → ℝ, (h z : EReal) ≤ f z}
    let fBar : (Fin n → ℝ) → EReal :=
      fun x => sSup ((fun h : ((Fin n → ℝ) → ℝ) => ((h x : ℝ) : EReal)) '' affineMinorants)
    ∀ x ∈ interior {z | f z < ⊤},
      f x = fBar x := by
  sorry

end «CAM-Bench-526»
