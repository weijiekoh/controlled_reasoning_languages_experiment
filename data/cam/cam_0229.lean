import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-229»

open scoped BigOperators

theorem convex_affineCombination_one_pos_rest_nonpos
    {m n : ℕ}
    (f : (Fin m → ℝ) → EReal)
    (hne_bot : ∀ y : Fin m → ℝ, f y ≠ ⊥)
    (hf : ConvexOn ℝ {y | f y < ⊤} (fun y => (f y).toReal))
    (x : Fin (n + 1) → (Fin m → ℝ))
    (hxdom : ∀ i : Fin (n + 1), f (x i) < ⊤)
    (hxne_bot : ∀ i : Fin (n + 1), f (x i) ≠ ⊥)
    (lam : Fin (n + 1) → ℝ)
    (hlam1 : 0 < lam 0)
    (hlamneg : ∀ i : Fin n, lam i.succ ≤ 0)
    (hlamsum : ∑ i, lam i = 1) :
    f (∑ i, lam i • x i) ≥ ((∑ i, lam i * (f (x i)).toReal : ℝ) : EReal) := by
  sorry

end «CAM-Bench-229»
