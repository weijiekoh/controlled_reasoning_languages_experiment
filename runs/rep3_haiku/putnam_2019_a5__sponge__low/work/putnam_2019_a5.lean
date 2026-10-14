import Mathlib

open Topology Filter

noncomputable abbrev putnam_2019_a5_solution : ℕ → ℕ := (fun p : ℕ => (p - 1) / 2)
/--
Let $p$ be an odd prime number, and let $\mathbb{F}_p$ denote the field of integers modulo $p$. Let $\mathbb{F}_p[x]$ be the ring of polynomials over $\mathbb{F}_p$, and let $q(x) \in \mathbb{F}_p[x]$ be given by $q(x)=\sum_{k=1}^{p-1} a_kx^k$, where $a_k=k^{(p-1)/2}\mod{p}$. Find the greatest nonnegative integer $n$ such that $(x-1)^n$ divides $q(x)$ in $\mathbb{F}_p[x]$.
-/
theorem putnam_2019_a5
  (p : ℕ)
  (q : Polynomial (ZMod p))
  (a : ℕ → ZMod p)
  (npoly : ℕ → Polynomial (ZMod p))
  (podd : Odd p)
  (pprime : p.Prime)
  (hq : ∀ k : ℕ, q.coeff k = a k)
  (ha0 : a 0 = 0 ∧ ∀ k > p - 1, a k = 0)
  (haother : ∀ k : Set.Icc 1 (p - 1), a k = ((k : ℕ) ^ ((p - 1) / 2)) % p)
  (hnpoly : ∀ n : ℕ, npoly n = ((Polynomial.X - 1 : Polynomial (ZMod p))) ^ n) :
  IsGreatest {n | npoly n ∣ q} (putnam_2019_a5_solution p) := by
  classical
  have := Fact.mk pprime
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp podd
  have hp2 := pprime.two_le
  obtain ⟨m, hm⟩ : ∃ m, m = (p - 1) / 2 := ⟨_, rfl⟩
  have hpm : p - 1 = 2 * m := by omega
  have hm1 : 1 ≤ m := by omega
  have hsol : putnam_2019_a5_solution p = m := by rw [hm]
  rw [hsol]
  have hsum0 : ∀ d, d < p - 1 → ∑ x : ZMod p, x ^ d = 0 := by
    intro d hd
    apply FiniteField.sum_pow_lt_card_sub_one (ZMod p) d
    rw [ZMod.card]; exact hd
  have hsumtop : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
    have h1 : ∀ x : ZMod p, x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
      intro x
      by_cases hx : x = 0
      · subst hx; rw [zero_pow (by omega)]; simp
      · rw [if_neg hx, ZMod.pow_card_sub_one_eq_one hx]; simp
    simp only [h1]
    simp [Finset.sum_sub_distrib, ZMod.card]
  have hL3 : ∀ P : Polynomial (ZMod p), P.natDegree < p →
      ∑ x : ZMod p, P.eval x = -P.coeff (p - 1) := by
    intro P hP
    rw [Finset.sum_congr rfl (fun x _ => Polynomial.eval_eq_sum_range' hP x), Finset.sum_comm]
    rw [Finset.sum_eq_single (p - 1)]
    · rw [← Finset.mul_sum, hsumtop, mul_neg_one]
    · intro i hi hne
      rw [Finset.mem_range] at hi
      rw [← Finset.mul_sum, hsum0 i (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hconv : ∀ D : Polynomial (ZMod p),
      ∑ j ∈ Finset.range p, D.eval (j : ZMod p) = ∑ x : ZMod p, D.eval x := by
    intro D
    apply Finset.sum_bij' (fun (j : ℕ) _ => (j : ZMod p)) (fun (x : ZMod p) _ => x.val)
    · intro a ha; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a ha; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    · intro a ha; rw [ZMod.natCast_zmod_val]
    · intro a ha; rfl
  have ha_zero : ∀ k, p ≤ k → a k = 0 := fun k hk => ha0.2 k (by omega)
  have hqsum : q = ∑ j ∈ Finset.range p, Polynomial.C (a j) * Polynomial.X ^ j := by
    ext n
    rw [hq n, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hn : n < p
    · rw [Finset.sum_eq_single n]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_range.mpr hn) h
    · rw [ha_zero n (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have : n ≠ j := by intro h; rw [Finset.mem_range] at hj; omega
      simp [this]
  have hA_val : ∀ j, j < p → a j = (j : ZMod p) ^ m := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [ha0.1, Nat.cast_zero, zero_pow (by omega)]
    · have h := haother ⟨j, Set.mem_Icc.mpr ⟨hj0, by omega⟩⟩
      simp only at h
      rw [← hm] at h
      rw [h, ZMod.natCast_mod, Nat.cast_pow]
  have hT : ∀ i, (Polynomial.taylor 1 q).coeff i
      = ∑ j ∈ Finset.range p, a j * ((j.choose i : ℕ) : ZMod p) := by
    intro i
    rw [hqsum, map_sum, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_1, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_one_pow]
  have hkey : ∀ i, ((i.factorial : ℕ) : ZMod p) * (Polynomial.taylor 1 q).coeff i
      = ∑ x : ZMod p, (descPochhammer (ZMod p) i * Polynomial.X ^ m).eval x := by
    intro i
    rw [hT i, Finset.mul_sum, ← hconv]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hA_val j hj, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hA : ∀ i, i < m → (Polynomial.taylor 1 q).coeff i = 0 := by
    intro i hi
    have hdeg : (descPochhammer (ZMod p) i * Polynomial.X ^ m).natDegree < p - 1 := by
      have : (descPochhammer (ZMod p) i * Polynomial.X ^ m).natDegree ≤ i + m := by
        refine Polynomial.natDegree_mul_le.trans ?_
        simp [descPochhammer_natDegree]
      omega
    have h0 := hkey i
    rw [hL3 (descPochhammer (ZMod p) i * Polynomial.X ^ m) (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, neg_zero] at h0
    have hf : ((i.factorial : ℕ) : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have := (Nat.Prime.dvd_factorial pprime).mp h
      omega
    exact (mul_eq_zero.mp h0).resolve_left hf
  have hB : (Polynomial.taylor 1 q).coeff m ≠ 0 := by
    intro h0
    have hc : (descPochhammer (ZMod p) m).coeff m = 1 := by
      have := (monic_descPochhammer (ZMod p) m).coeff_natDegree
      rwa [descPochhammer_natDegree] at this
    have hcoef : (descPochhammer (ZMod p) m * Polynomial.X ^ m).coeff (p - 1) = 1 := by
      rw [hpm, show 2 * m = m + m by ring, Polynomial.coeff_mul_X_pow, hc]
    have hdegB : (descPochhammer (ZMod p) m * Polynomial.X ^ m).natDegree ≤ m + m := by
      refine Polynomial.natDegree_mul_le.trans ?_
      simp [descPochhammer_natDegree]
    have h1 := hkey m
    rw [h0, mul_zero, hL3 (descPochhammer (ZMod p) m * Polynomial.X ^ m) (by omega),
      hcoef] at h1
    exact (neg_ne_zero.mpr one_ne_zero : (-1 : ZMod p) ≠ 0) h1.symm
  have hdivfwd : ∀ n, ((Polynomial.X - 1 : Polynomial (ZMod p))) ^ n ∣ q → (Polynomial.X ^ n : Polynomial (ZMod p)) ∣ Polynomial.taylor 1 q := by
    rintro n ⟨r, hr⟩
    have h1 : Polynomial.taylor 1 (((Polynomial.X - 1 : Polynomial (ZMod p))) ^ n) = (Polynomial.X ^ n : Polynomial (ZMod p)) := by
      simp [Polynomial.taylor_apply, Polynomial.pow_comp]
    rw [hr, Polynomial.taylor_mul, h1]
    exact dvd_mul_right _ _
  have hdivbwd : ∀ n, (Polynomial.X ^ n : Polynomial (ZMod p)) ∣ Polynomial.taylor 1 q → ((Polynomial.X - 1 : Polynomial (ZMod p))) ^ n ∣ q := by
    rintro n ⟨s, hs⟩
    have h2 : Polynomial.taylor (-1) (Polynomial.X ^ n : Polynomial (ZMod p)) = ((Polynomial.X - 1 : Polynomial (ZMod p))) ^ n := by
      simp [Polynomial.taylor_apply, Polynomial.pow_comp, sub_eq_add_neg]
    have hq' : q = Polynomial.taylor (-1) (Polynomial.taylor 1 q) := by
      rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
    refine ⟨Polynomial.taylor (-1) s, ?_⟩
    rw [hq', hs, Polynomial.taylor_mul, h2]
  constructor
  · show npoly m ∣ q
    rw [hnpoly]
    exact hdivbwd m (Polynomial.X_pow_dvd_iff.mpr fun d hd => hA d hd)
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly] at hn'
    by_contra hlt
    push_neg at hlt
    have h1 : ((Polynomial.X - 1 : Polynomial (ZMod p))) ^ (m + 1) ∣ q := (pow_dvd_pow _ hlt).trans hn'
    have h2 := hdivfwd (m + 1) h1
    rw [Polynomial.X_pow_dvd_iff] at h2
    exact hB (h2 m (Nat.lt_succ_self m))
