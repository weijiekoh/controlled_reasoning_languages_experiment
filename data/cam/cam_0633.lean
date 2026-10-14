import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-633»

open scoped BigOperators

theorem phi_convex_of_convex_functions
    {n : ℕ} {m : ℕ}
    (f : Fin (m + 1) → (Fin n → ℝ) → ℝ) (α : ℝ)
    (hdiff₀ : Differentiable ℝ (f 0))
    (hdiff : ∀ i : Fin m, Differentiable ℝ (f i.succ))
    (hf₀ : ConvexOn ℝ Set.univ (f 0))
    (hf : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i.succ))
    (hα : 0 < α) :
    ConvexOn ℝ Set.univ
      (fun x =>
        f 0 x + α * sSup (((fun i : Fin (m + 1) => if i = 0 then (0 : ℝ) else f i x) '' Set.univ))) := by
  sorry

end «CAM-Bench-633»
