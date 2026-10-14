import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-112»

open scoped BigOperators

theorem quadratic_line_search_minimizer
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (b xₖ pₖ : Fin n → ℝ)
    (hQsymm : Q.IsSymm) (hQpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Q.mulVec v))
    (hpₖ : pₖ ≠ 0) :
    let f : (Fin n → ℝ) → ℝ :=
      fun x => (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) - dotProduct b x
    let φ : ℝ → ℝ := fun α => f (xₖ + α • pₖ)
    let gradf : (Fin n → ℝ) → (Fin n → ℝ) := fun x => Q.mulVec x - b
    let gradfₖ : Fin n → ℝ := gradf xₖ
    let αₖ : ℝ := -(dotProduct gradfₖ pₖ) / (dotProduct pₖ (Q.mulVec pₖ))
    ∀ α : ℝ, φ αₖ ≤ φ α := by
  sorry

end «CAM-Bench-112»
