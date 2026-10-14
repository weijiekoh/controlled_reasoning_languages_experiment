import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-756»

open Matrix

theorem quadratic_has_unique_global_minimum_iff_posDef
    {n : Type _} [Fintype n] [DecidableEq n] [Nonempty n]
    (c : ℝ) (g : n → ℝ) (B : Matrix n n ℝ)
    (hsymm : B.IsSymm) :
    ((let m : (n → ℝ) → ℝ := fun d =>
        c + dotProduct g d + (1 / 2 : ℝ) * dotProduct d (fun i => ∑ j, B i j * d j)
      ∃! d₀ : n → ℝ, ∀ d : n → ℝ, m d₀ ≤ m d) ↔
      PosDef B) := by
  sorry

end «CAM-Bench-756»
