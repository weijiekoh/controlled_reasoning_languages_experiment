import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-104»

theorem quadratic_form_convex_of_posSemidef
    (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQsymm : Qᵀ = Q)
    (hQpsd : ∀ z : Fin n → ℝ, 0 ≤ dotProduct z (Q.mulVec z)) :
    ConvexOn ℝ Set.univ (fun x : Fin n → ℝ => dotProduct x (Q.mulVec x)) := by
  sorry

end «CAM-Bench-104»
