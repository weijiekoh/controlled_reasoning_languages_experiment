import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-530»

theorem g_homogeneous
    {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    : ∀ (x : Fin n → ℝ) (t : ℝ), 0 ≤ t →
        (let g : (Fin n → ℝ) → WithBot ℝ :=
          fun x =>
            sInf {r : WithBot ℝ | ∃ α : ℝ, 0 < α ∧ r = ((f (α • x) / α : ℝ) : WithBot ℝ)}
         ; g (t • x) = ((t : ℝ) : WithBot ℝ) * g x) := by
  sorry

end «CAM-Bench-530»
