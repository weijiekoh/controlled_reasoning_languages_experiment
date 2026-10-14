import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-542»

def supportFunction {n : ℕ} (C : Set (Fin n → ℝ)) : (Fin n → ℝ) → EReal :=
  fun y => sSup ((fun x : Fin n → ℝ => (∑ i, y i * x i : ℝ)) '' C)

theorem subset_iff_supportFunction_le
    {n : ℕ} (A B : Set (Fin n → ℝ))
    (hB_closed : IsClosed B) (hB_convex : Convex ℝ B) :
    A ⊆ B ↔ ∀ y : Fin n → ℝ, supportFunction A y ≤ supportFunction B y := by
  sorry

end «CAM-Bench-542»
