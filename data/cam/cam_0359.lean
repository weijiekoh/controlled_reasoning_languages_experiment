import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-359»

def bregmanDivergence
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (grad_f : (Fin n → ℝ) → (Fin n → ℝ))
    (x y : Fin n → ℝ) : ℝ :=
  f x - f y - ∑ i : Fin n, (grad_f y i) * (x i - y i)

theorem bregmanDivergence_nonneg
    {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (f' : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_diff : Differentiable ℝ f)
    (hf_strictConvex : StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f)
    (hf'_grad : ∀ y : Fin n → ℝ, f' y = fun i => (fderiv ℝ f y) (Pi.single i (1 : ℝ)))
    (x y : Fin n → ℝ) :
    0 ≤ bregmanDivergence f f' x y := by
  sorry

end «CAM-Bench-359»
