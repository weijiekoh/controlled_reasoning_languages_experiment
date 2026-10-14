import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-223»

open scoped BigOperators

theorem job_allocation_convex_optimization_problem
    {J P n : ℕ}
    (R : Fin P → Fin J → ℝ)
    (psi : Fin P → (Fin n → ℝ) → ℝ → ℝ)
    (lmax w ttar : Fin J → ℝ)
    (xtot : Fin n → ℝ)
    (hpsi_convex :
      ∀ p : Fin P, ConvexOn ℝ Set.univ (fun z : (Fin n → ℝ) × ℝ => psi p z.1 z.2))
    (hR_nonneg : ∀ p j, 0 ≤ R p j)
    (hw : ∀ j : Fin J, 0 < w j) :
    ConvexOn ℝ Set.univ
        (fun t : Fin J → ℝ =>
          ∑ j, w j * max (ttar j - t j) 0) ∧
      Convex ℝ
        {tx : (Fin J → ℝ) × (Fin P → Fin n → ℝ) |
          (∀ j : Fin J, 0 ≤ tx.1 j) ∧
          (∀ p : Fin P, ∀ i : Fin n, 0 ≤ tx.2 p i) ∧
          (∀ j : Fin J,
            ∑ p, psi p (tx.2 p) (∑ k, R p k * tx.1 k) * R p j ≤ lmax j) ∧
          (∀ i : Fin n, ∑ p, tx.2 p i ≤ xtot i)} := by
  sorry

end «CAM-Bench-223»
