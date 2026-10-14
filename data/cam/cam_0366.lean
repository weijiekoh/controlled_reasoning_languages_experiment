import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-366»

def IsEuclideanDistanceMatrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
    ∃ m : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin m),
      ∀ i j : Fin n, X i j = ‖p i - p j‖ ^ 2

theorem exp_neg_edm_posSemidef
    {n : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : IsEuclideanDistanceMatrix X) :
    ∀ y : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, y i * Real.exp (-(X i j)) * y j := by
  sorry

end «CAM-Bench-366»
