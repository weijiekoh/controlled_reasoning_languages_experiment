import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-119»

open scoped Matrix

theorem gamma_le_one_for_spd
    {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℝ) (g : n → ℝ)
    (h_symm : B.IsSymm) (h_pos : B.PosDef) (hg : g ≠ 0) :
    (dotProduct g g) ^ 2 / (dotProduct g (B.mulVec g) * dotProduct g (B⁻¹.mulVec g)) ≤ 1 ∧
      ((dotProduct g g) ^ 2 / (dotProduct g (B.mulVec g) * dotProduct g (B⁻¹.mulVec g)) = 1 →
        (∃ c : ℝ, B.mulVec g = c • g) ∧
        (∃ d : ℝ, B⁻¹.mulVec g = d • g)) := by
  sorry

end «CAM-Bench-119»
