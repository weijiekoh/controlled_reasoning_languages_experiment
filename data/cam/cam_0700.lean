import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-700»

namespace Exercise_8_9

open scoped Matrix

def IsEuclideanDistanceMatrix {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  D.IsSymm ∧
  (∀ i : Fin n, D i i = 0) ∧
  ∃ (m : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin m)),
    ∀ i j : Fin n, D i j = ‖x i - x j‖ ^ 2

theorem euclidean_distance_matrix_iff_centered_gram_psd
    {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) :
    IsEuclideanDistanceMatrix D ↔
      (D.IsSymm ∧
        (∀ i : Fin n, D i i = 0) ∧
        ∃ (m : ℕ) (y : Fin n → EuclideanSpace ℝ (Fin m)),
          (∑ i, y i = 0) ∧
          ∀ i j : Fin n, D i j = ‖y i - y j‖ ^ 2) := by
  sorry
end Exercise_8_9

end «CAM-Bench-700»
