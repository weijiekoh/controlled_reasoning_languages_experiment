import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-527»

def epigraph {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  { p | f p.1 ≤ p.2 }

theorem closed_convex_eq_sup_affine_minorants
    {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ)
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f)) :
    f =
      fun x =>
        sSup {r : WithTop ℝ |
          ∃ a : Fin n → ℝ, ∃ b : ℝ,
            (∀ z : Fin n → ℝ, (((∑ i, a i * z i) + b : ℝ) : WithTop ℝ) ≤ f z) ∧
            r = (((∑ i, a i * x i) + b : ℝ) : WithTop ℝ)} := by
  sorry

end «CAM-Bench-527»
