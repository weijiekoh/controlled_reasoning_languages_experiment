import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-446»

theorem preimage_polyhedron_linearFractional
    {m n p : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ)
    (c : Fin m → ℝ)
    (d : ℝ)
    (G : Matrix (Fin p) (Fin n) ℝ)
    (h : Fin p → ℝ) :
    {x : Fin m → ℝ |
        0 < dotProduct c x + d ∧
        ∀ i : Fin p, (G.mulVec (fun j => ((A.mulVec x) j + b j) / (dotProduct c x + d))) i ≤ h i} =
    {x : Fin m → ℝ |
        (∀ i : Fin p, (G.mulVec (fun j => (A.mulVec x) j + b j)) i ≤ h i * (dotProduct c x + d)) ∧
        0 < dotProduct c x + d} := by
  sorry

end «CAM-Bench-446»
