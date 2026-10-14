import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-548»

def conjugate {n : Type*} [Fintype n] (h : (n → ℝ) → EReal) : (n → ℝ) → EReal :=
  fun y => sSup {t : EReal | ∃ x : n → ℝ, t = (((∑ i, y i * x i : ℝ) : EReal) - h x)}

theorem conjugate_add_affine_eq_shift_sub
    {n : Type*} [Fintype n]
    (f : (n → ℝ) → EReal) (c : n → ℝ) (d : ℝ)
    (hf : ∀ x y : n → ℝ, ∀ theta : ℝ,
      0 ≤ theta → theta ≤ 1 →
      f (fun i => theta * x i + (1 - theta) * y i) ≤
        ((theta : EReal) * f x + (((1 - theta : ℝ) : EReal) * f y)))
    (g : (n → ℝ) → EReal)
    (hg : g = fun x => f x + (((∑ i, c i * x i : ℝ) : EReal) + (d : EReal))) :
    ∀ y : n → ℝ, conjugate g y = conjugate f (fun i => y i - c i) - (d : EReal) := by
  sorry

end «CAM-Bench-548»
