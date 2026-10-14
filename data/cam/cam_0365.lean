import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-365»

def IsEuclideanDistanceMatrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (m : ℕ := 0) : Prop :=
  X.IsSymm ∧ ∃ m' : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin m'), ∀ i j, X i j = ‖p i - p j‖ ^ 2

def HasCenteringCondition {n m : ℕ} (p : Fin n → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∑ i, p i = 0

open scoped Matrix BigOperators

theorem euclideanDistanceMatrix_iff_zero_diag_and_centered_projection_nsd {n : ℕ}
    (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) :
    IsEuclideanDistanceMatrix X ↔
      (∀ i : Fin n, X i i = 0) ∧
        let J : Matrix (Fin n) (Fin n) ℝ :=
          1 - ((1 : ℝ) / n) • fun _ _ => (1 : ℝ)
        ∀ v : Fin n → ℝ,
          v ⬝ᵥ ((J * X * J).mulVec v) ≤ 0 := by
  sorry

end «CAM-Bench-365»
