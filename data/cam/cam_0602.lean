import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-602»

theorem strict_separating_hyperplane_iff_soc_feasible
    {n K L : ℕ}
    (Ppos : Fin K → Matrix (Fin n) (Fin n) ℝ)
    (qpos : Fin K → EuclideanSpace ℝ (Fin n))
    (Pneg : Fin L → Matrix (Fin n) (Fin n) ℝ)
    (qneg : Fin L → EuclideanSpace ℝ (Fin n))
    (hPpos : ∀ i, (Ppos i).IsSymm)
    (hPneg : ∀ i, (Pneg i).IsSymm) :
    (∃ a : EuclideanSpace ℝ (Fin n), ∃ b : ℝ,
      (∀ i (u : EuclideanSpace ℝ (Fin n)),
        ‖u‖ ≤ 1 → 0 < dotProduct a ((Ppos i).mulVec u + qpos i) + b) ∧
      (∀ i (u : EuclideanSpace ℝ (Fin n)),
        ‖u‖ ≤ 1 → dotProduct a ((Pneg i).mulVec u + qneg i) + b < 0)) ↔
    (∃ a : EuclideanSpace ℝ (Fin n), ∃ b : ℝ,
      (∀ i, -‖(Ppos i).transpose.mulVec a‖ + dotProduct a (qpos i) + b ≥ 1) ∧
      (∀ i, ‖(Pneg i).transpose.mulVec a‖ + dotProduct a (qneg i) + b ≤ -1)) := by
  sorry

end «CAM-Bench-602»
