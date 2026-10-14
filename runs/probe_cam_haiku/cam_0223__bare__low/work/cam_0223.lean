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
  constructor
  · have key : ∀ j, ConvexOn ℝ Set.univ (fun t : Fin J → ℝ => w j * max (ttar j - t j) 0) := by
      intro j
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 : ttar j - (a * x j + b * y j) = a * (ttar j - x j) + b * (ttar j - y j) := by
        linear_combination (-(ttar j)) * hab
      have hm : max (ttar j - (a * x j + b * y j)) 0 ≤ a * max (ttar j - x j) 0 + b * max (ttar j - y j) 0 := by
        rw [h1]
        apply max_le
        · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
        · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
      have := mul_le_mul_of_nonneg_left hm (hw j).le
      nlinarith
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    exact (key j).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hx
    obtain ⟨h1', h2', h3', h4'⟩ := hy
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      simp only [Prod.smul_fst, Prod.fst_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (h1 j)) (mul_nonneg hb (h1' j))
    · intro p i
      simp only [Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (h2 p i)) (mul_nonneg hb (h2' p i))
    · intro j
      show ∑ p, psi p (a • x.2 p + b • y.2 p) (∑ k, R p k * (a • x.1 k + b • y.1 k)) * R p j ≤ lmax j
      have hp : ∀ p, psi p (a • x.2 p + b • y.2 p) (∑ k, R p k * (a • x.1 k + b • y.1 k))
          ≤ a * psi p (x.2 p) (∑ k, R p k * x.1 k) + b * psi p (y.2 p) (∑ k, R p k * y.1 k) := by
        intro p
        have hs : ∑ k, R p k * (a • x.1 k + b • y.1 k)
            = a * (∑ k, R p k * x.1 k) + b * (∑ k, R p k * y.1 k) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          simp only [smul_eq_mul]
          ring
        have := (hpsi_convex p).2 (Set.mem_univ (x.2 p, ∑ k, R p k * x.1 k))
          (Set.mem_univ (y.2 p, ∑ k, R p k * y.1 k)) ha hb hab
        simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk] at this
        rw [hs]
        exact this
      calc ∑ p, psi p (a • x.2 p + b • y.2 p) (∑ k, R p k * (a • x.1 k + b • y.1 k)) * R p j
          ≤ ∑ p, (a * (psi p (x.2 p) (∑ k, R p k * x.1 k) * R p j)
                + b * (psi p (y.2 p) (∑ k, R p k * y.1 k) * R p j)) := by
            apply Finset.sum_le_sum
            intro p _
            have := mul_le_mul_of_nonneg_right (hp p) (hR_nonneg p j)
            linarith
        _ = a * (∑ p, psi p (x.2 p) (∑ k, R p k * x.1 k) * R p j)
              + b * (∑ p, psi p (y.2 p) (∑ k, R p k * y.1 k) * R p j) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        _ ≤ a * lmax j + b * lmax j :=
            add_le_add (mul_le_mul_of_nonneg_left (h3 j) ha) (mul_le_mul_of_nonneg_left (h3' j) hb)
        _ = lmax j := by rw [← add_mul, hab, one_mul]
    · intro i
      show ∑ p, (a • x.2 p + b • y.2 p) i ≤ xtot i
      have e : ∑ p, (a • x.2 p + b • y.2 p) i = a * (∑ p, x.2 p i) + b * (∑ p, y.2 p i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib]
      rw [e]
      calc a * (∑ p, x.2 p i) + b * (∑ p, y.2 p i)
          ≤ a * xtot i + b * xtot i :=
            add_le_add (mul_le_mul_of_nonneg_left (h4 i) ha) (mul_le_mul_of_nonneg_left (h4' i) hb)
        _ = xtot i := by rw [← add_mul, hab, one_mul]

end «CAM-Bench-223»
