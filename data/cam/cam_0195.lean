import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-195»

open scoped BigOperators

theorem complianceEnergy_convexOn
    {m n : ℕ}
    (K : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hKsymm : ∀ i, (K i).IsSymm)
    (hKpsd : ∀ i, Matrix.PosSemidef (K i))
    (f : Fin n → ℝ) :
    ConvexOn ℝ
      {x : Fin m → ℝ | Matrix.PosDef (∑ i, x i • K i)}
      (fun x => (1 / 2 : ℝ) * dotProduct f (((∑ i, x i • K i)⁻¹).mulVec f)) := by
  sorry

end «CAM-Bench-195»
