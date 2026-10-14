import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-239»

open scoped BigOperators

theorem convex_permutation_invariant_doubly_stochastic_le
    {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_perm :
      ∀ σ : Equiv.Perm (Fin n), ∀ x : Fin n → ℝ, f ((σ.permMatrix ℝ).mulVec x) = f x)
    (hS_nonneg : ∀ i j : Fin n, 0 ≤ S i j)
    (hS_row_sum : ∀ i : Fin n, ∑ j, S i j = 1)
    (hS_col_sum : ∀ j : Fin n, ∑ i, S i j = 1)
    (lam : Fin m → ℝ)
    (hlam_nonneg : ∀ k : Fin m, 0 ≤ lam k)
    (P : Fin m → Equiv.Perm (Fin n))
    (hlam_sum : ∑ k, lam k = 1)
    (hS : S = ∑ k, (lam k) • ((P k).permMatrix ℝ))
    (x : Fin n → ℝ) :
    f (S.mulVec x) ≤ f x := by
  sorry

end «CAM-Bench-239»
