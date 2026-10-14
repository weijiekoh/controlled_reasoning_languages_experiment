import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-363»

open scoped BigOperators

def IsEuclideanDistanceMatrix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  X.IsSymm ∧
    ∃ m : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin m),
      ∀ i j : Fin n, X i j = ‖p i - p j‖ ^ 2

theorem isEuclideanDistanceMatrix_iff_exists_psd_representation {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) :
    IsEuclideanDistanceMatrix X ↔
      ∃ Y : Matrix (Fin n) (Fin n) ℝ,
        Y.IsSymm ∧
        Y.PosSemidef ∧
        ∀ i j : Fin n, X i j = Y i i + Y j j - 2 * Y i j := by
  sorry

end «CAM-Bench-363»
