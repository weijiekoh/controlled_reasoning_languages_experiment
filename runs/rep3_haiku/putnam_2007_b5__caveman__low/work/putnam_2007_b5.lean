import Mathlib

open Set Nat Function

/--
Let $k$ be a positive integer. Prove that there exist polynomials $P_0(n), P_1(n), \dots, P_{k-1}(n)$ (which may depend on $k$) such that for any integer $n$,
\[
\left\lfloor \frac{n}{k} \right\rfloor^k = P_0(n) + P_1(n) \left\lfloor
\frac{n}{k} \right\rfloor + \cdots + P_{k-1}(n) \left\lfloor \frac{n}{k}
\right\rfloor^{k-1}.
\]
($\lfloor a \rfloor$ means the largest integer $\leq a$.)
-/
theorem putnam_2007_b5
(k : ℕ) (kpos : k > 0) :
(∃ P : Finset.range k → Polynomial ℝ, ∀ n : ℤ, ⌊(n : ℝ) / k⌋ ^ k = ∑ i : Finset.range k, (P i).eval (n : ℝ) * ⌊(n : ℝ) / k⌋ ^ (i : ℕ)) :=
 by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Polynomial (Polynomial ℝ), F = fun j =>
      Polynomial.C (Polynomial.X : Polynomial ℝ)
        - Polynomial.C ((k:ℕ) : Polynomial ℝ) * (Polynomial.X : Polynomial (Polynomial ℝ))
        - Polynomial.C ((j:ℕ) : Polynomial ℝ) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Polynomial (Polynomial ℝ), g = ∏ j ∈ Finset.range k, F j := ⟨_, rfl⟩
  have hFdeg : ∀ j, (F j).natDegree = 1 := by
    intro j
    have hle : (F j).natDegree ≤ 1 := by subst hF; simp only []; compute_degree
    refine le_antisymm hle (Polynomial.le_natDegree_of_ne_zero ?_)
    subst hF
    simp
    exact_mod_cast kpos.ne'
  have hFlc : ∀ j, (F j).leadingCoeff = -((k:ℕ) : Polynomial ℝ) := by
    intro j
    rw [Polynomial.leadingCoeff, hFdeg j]
    subst hF
    simp [Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_C_mul]
  have hne : ∀ j, F j ≠ 0 := fun j h => by
    have := hFdeg j; rw [h, Polynomial.natDegree_zero] at this; exact absurd this (by norm_num)
  have hgdeg : g.natDegree = k := by
    rw [hg, Polynomial.natDegree_prod _ _ (fun j _ => hne j)]
    simp [hFdeg]
  have hlc : g.leadingCoeff = (-((k:ℕ) : Polynomial ℝ))^k := by
    rw [hg, Polynomial.leadingCoeff_prod]
    simp [hFlc]
  have hcoef : g.coeff k = (-((k:ℕ) : Polynomial ℝ))^k := by
    rw [← hlc, Polynomial.leadingCoeff, hgdeg]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(((-(k:ℝ))^k)⁻¹) := ⟨_, rfl⟩
  refine ⟨fun i => Polynomial.C c * g.coeff (i:ℕ), ?_⟩
  intro n
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = ⌊(n:ℝ)/k⌋ := ⟨_, rfl⟩
  rw [← hm]
  have hkpos : (0:ℝ) < k := by exact_mod_cast kpos
  have h1 : (m:ℝ) ≤ (n:ℝ)/k := by rw [hm]; exact Int.floor_le _
  have h2 : (n:ℝ)/k < m + 1 := by rw [hm]; exact Int.lt_floor_add_one _
  rw [le_div_iff₀ hkpos] at h1
  rw [div_lt_iff₀ hkpos] at h2
  have h1' : m * (k:ℤ) ≤ n := by exact_mod_cast (show (m:ℝ) * (k:ℝ) ≤ n by linarith)
  have h2' : (n:ℤ) < (m+1) * (k:ℤ) := by exact_mod_cast (show (n:ℝ) < ((m:ℝ)+1) * (k:ℝ) by linarith)
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = n - m * k := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by linarith
  have hrk : r < k := by linarith
  have hj : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
  have hjk : r.toNat < k := by omega
  have hjr : ((r.toNat : ℕ) : ℝ) = (n:ℝ) - m * k := by
    have : ((r.toNat : ℕ) : ℝ) = (r:ℝ) := by exact_mod_cast hj
    rw [this, hr]; push_cast; ring
  have hn : g.natDegree < k+1 := by omega
  have key := Polynomial.eval₂_eq_sum_range' (Polynomial.evalRingHom (n:ℝ)) hn (m:ℝ)
  have hzero : Polynomial.eval₂ (Polynomial.evalRingHom (n:ℝ)) (m:ℝ) g = 0 := by
    rw [hg, ← Polynomial.coe_eval₂RingHom, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hjk)
    rw [hF]
    simp
    linarith [hjr]
  rw [key, Finset.sum_range_succ, hcoef] at hzero
  simp at hzero
  have hpow : (-(k:ℝ))^k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hkpos.ne')
  rw [Finset.sum_coe_sort (Finset.range k) (fun i => (Polynomial.C c * g.coeff i).eval (n:ℝ) * (m:ℝ)^i)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, ← Finset.mul_sum]
  have hS : ∑ x ∈ Finset.range k, Polynomial.eval (n:ℝ) (g.coeff x) * (m:ℝ)^x = -((-(k:ℝ))^k * (m:ℝ)^k) := by
    push_cast at hzero; linarith
  simp only [mul_assoc, ← Finset.mul_sum, hS]
  rw [hc]
  field_simp
