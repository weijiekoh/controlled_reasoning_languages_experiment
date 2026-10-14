import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-471»

def traceInnerProduct {n : Type} [Fintype n] [DecidableEq n]
    (A B : {M : Matrix n n ℝ // M.IsSymm}) : ℝ :=
  Matrix.trace (A.1 * B.1)

def IsEuclideanDistanceMatrix {n : Type} [Fintype n] [DecidableEq n] (D : Matrix n n ℝ) : Prop :=
  D.IsSymm ∧
    (∀ i, D i i = 0) ∧
    ∀ x : n → ℝ, (∑ i, x i) = 0 →
      dotProduct x (fun i => ∑ j, D i j * x j) ≤ 0

open scoped RealInnerProductSpace

def dualCone {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) : Set E :=
  {y | ∀ x ∈ K, 0 ≤ ⟪y, x⟫}

theorem dualCone_of_euclideanDistanceMatrices_eq_vwvT_add_diag
    {n : ℕ} (hn : 1 < n)
    [NormedAddCommGroup {M : Matrix (Fin n) (Fin n) ℝ // M.IsSymm}]
    [InnerProductSpace ℝ {M : Matrix (Fin n) (Fin n) ℝ // M.IsSymm}]
    (htrace : ∀ A B : {M : Matrix (Fin n) (Fin n) ℝ // M.IsSymm},
      ⟪A, B⟫ = traceInnerProduct A B) :
    let K : Set {M : Matrix (Fin n) (Fin n) ℝ // M.IsSymm} :=
      {D | (∀ i, D.1 i i = 0) ∧
        ∀ x : Fin n → ℝ, (∑ i, x i) = 0 →
          dotProduct x (fun i => ∑ j, D.1 i j * x j) ≤ 0}
    ∃ V : Matrix (Fin n) (Fin (n - 1)) ℝ,
    Convex ℝ K ∧
      (∀ a b, 0 ≤ a → 0 ≤ b → ∀ A ∈ K, ∀ B ∈ K, a • A + b • B ∈ K) ∧
      dualCone K =
        {Y : {M : Matrix (Fin n) (Fin n) ℝ // M.IsSymm} |
          ∃ W : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ, ∃ u : Fin n → ℝ,
            Y.1 = V * W * V.transpose + Matrix.diagonal u ∧
            W.IsSymm ∧
            ∀ x : Fin (n - 1) → ℝ, 0 ≤ dotProduct x (W.mulVec x)} := by
  sorry

end «CAM-Bench-471»
