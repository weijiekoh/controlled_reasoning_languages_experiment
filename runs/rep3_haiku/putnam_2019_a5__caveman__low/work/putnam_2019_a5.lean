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
  (hnpoly : ∀ n : ℕ, npoly n = (Polynomial.X - 1) ^ n) :
  IsGreatest {n | npoly n ∣ q} (putnam_2019_a5_solution p) := by
  open Polynomial in
  obtain ⟨hp1, hp2⟩ := ha0
  have : Fact p.Prime := ⟨pprime⟩
  have hp3 : 3 ≤ p := by
    obtain ⟨t, ht⟩ := podd; have := pprime.two_le; omega
  have : NeZero p := ⟨by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, m = (p - 1) / 2 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hpm : p - 1 = 2 * m := by obtain ⟨t, ht⟩ := podd; omega
  -- a k = k^m for k < p
  have ha : ∀ k, k < p → a k = (k : ZMod p) ^ m := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [hp1, zero_pow (by omega : m ≠ 0)]
    · have h := haother ⟨k, Set.mem_Icc.mpr ⟨hpos, by omega⟩⟩
      rw [h, ZMod.natCast_mod, Nat.cast_pow, ← hm]
  -- q as a finite sum
  have hqsum : q = ∑ k ∈ Finset.range p, C (a k) * X ^ k := by
    ext n
    rw [hq, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hn : n < p
    · simp [hn]
    · rw [if_neg (by simpa using hn), hp2 n (by omega)]
  -- Taylor coefficients at 1 are the hasse derivatives
  have e1 : ∀ n : ℕ, taylor (1 : ZMod p) ((X - 1) ^ n) = X ^ n := by
    intro n; simp [taylor_apply, pow_comp]
  have e2 : ∀ n : ℕ, taylor (-1 : ZMod p) (X ^ n) = (X - 1) ^ n := by
    intro n; simp [taylor_apply, sub_eq_add_neg]
  have hD : ∀ n, (X - 1) ^ n ∣ q ↔ ∀ d < n, (hasseDeriv d q).eval 1 = 0 := by
    intro n
    have step : (X - 1) ^ n ∣ q ↔ X ^ n ∣ taylor 1 q := by
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨taylor 1 g, by rw [hg, taylor_mul, e1]⟩
      · rintro ⟨h, hh⟩
        refine ⟨taylor (-1) h, ?_⟩
        have hq' : q = taylor (-1) (taylor 1 q) := by
          rw [taylor_taylor, show (-1 : ZMod p) + 1 = 0 by ring, taylor_zero]
        rw [hq', hh, taylor_mul, e2]
    rw [step, X_pow_dvd_iff]
    simp only [taylor_coeff]
  -- evaluation of hasse derivatives at 1
  have hev : ∀ j, (hasseDeriv j q).eval 1 = ∑ k ∈ Finset.range p, a k * ((k.choose j : ℕ) : ZMod p) := by
    intro j
    rw [hqsum, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (C (a k) * X ^ k : (ZMod p)[X]) = monomial k (a k) from by
      rw [X_pow_eq_monomial, C_mul_monomial, mul_one]]
    rw [hasseDeriv_monomial, eval_monomial, one_pow, mul_one]
    ring
  -- sums of powers over ZMod p
  have hconv : ∀ e : ℕ, ∑ k ∈ Finset.range p, (k : ZMod p) ^ e = ∑ x : ZMod p, x ^ e := by
    intro e
    refine Finset.sum_nbij (fun k : ℕ => (k : ZMod p)) ?_ ?_ ?_ ?_
    · intro k _; exact Finset.mem_univ _
    · intro x hx y hy hxy
      have := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
      rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_coe.mp hx)), Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_coe.mp hy))] at this
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro k _; rfl
  have Tlow : ∀ e, 1 ≤ e → e < p - 1 → ∑ k ∈ Finset.range p, (k : ZMod p) ^ e = 0 := by
    intro e h1 h2
    rw [hconv]
    have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) e (by rw [ZMod.card]; omega)
    exact this
  have Tfull : ∑ k ∈ Finset.range p, (k : ZMod p) ^ (p - 1) = -1 := by
    rw [hconv]
    have h0 : (0 : ZMod p) ^ (p - 1) = 0 := zero_pow (by omega)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)), h0, zero_add]
    rw [Finset.sum_congr rfl (fun x hx => ZMod.pow_card_sub_one_eq_one (Finset.ne_of_mem_erase hx))]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  -- hasse derivative identities
  have hP : ∀ j k : ℕ, ((j.factorial : ℕ) : ZMod p) * ((k.choose j : ℕ) : ZMod p)
      = (descPochhammer (ZMod p) j).eval (k : ZMod p) := by
    intro j k
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  have L : ∀ j, j ≤ m → ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * (descPochhammer (ZMod p) j).eval (k : ZMod p)
      = if j = m then -1 else 0 := by
    intro j hj
    have hdeg : (descPochhammer (ZMod p) j).natDegree < j + 1 := by
      rw [descPochhammer_natDegree]; omega
    calc ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * (descPochhammer (ZMod p) j).eval (k : ZMod p)
        = ∑ k ∈ Finset.range p, ∑ i ∈ Finset.range (j + 1),
            (descPochhammer (ZMod p) j).coeff i * (k : ZMod p) ^ (m + i) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ Finset.range (j + 1), (descPochhammer (ZMod p) j).coeff i *
            ∑ k ∈ Finset.range p, (k : ZMod p) ^ (m + i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range (j + 1), (descPochhammer (ZMod p) j).coeff i *
            (if i = m then -1 else 0) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi' := Finset.mem_range.mp hi
          by_cases him : i = m
          · subst him
            rw [if_pos rfl, show i + i = p - 1 by omega, Tfull]
          · rw [Tlow (m + i) (by omega) (by omega), if_neg him, mul_zero]
      _ = if j = m then -1 else 0 := by
          by_cases hjm : j = m
          · subst hjm
            have hmon := monic_descPochhammer (ZMod p) j
            have hnd : (descPochhammer (ZMod p) j).natDegree = j := descPochhammer_natDegree _ _
            have hc : (descPochhammer (ZMod p) j).coeff j = 1 := by
              have := hmon.coeff_natDegree; rwa [hnd] at this
            have hz : ∑ i ∈ Finset.range j, (descPochhammer (ZMod p) j).coeff i *
                (if i = j then (-1 : ZMod p) else 0) = 0 :=
              Finset.sum_eq_zero (fun i hi => by
                have := Finset.mem_range.mp hi
                rw [if_neg (by omega), mul_zero])
            rw [Finset.sum_range_succ, hz, zero_add, hc]
            simp
          · rw [if_neg hjm]
            apply Finset.sum_eq_zero
            intro i hi
            have := Finset.mem_range.mp hi
            rw [if_neg (by omega), mul_zero]
  have hJ : ∀ j, j ≤ m → ((j.factorial : ℕ) : ZMod p) * ∑ k ∈ Finset.range p, a k * ((k.choose j : ℕ) : ZMod p)
      = if j = m then -1 else 0 := by
    intro j hj
    rw [← L j hj, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [ha k (Finset.mem_range.mp hk), ← hP j k]
    ring
  have hfac : ∀ j, j < p → ((j.factorial : ℕ) : ZMod p) ≠ 0 := by
    intro j hj h
    have hd : p ∣ j.factorial := (ZMod.natCast_eq_zero_iff _ _).mp h
    have := (Nat.Prime.dvd_factorial pprime).mp hd
    omega
  have hzero : ∀ d < m, (hasseDeriv d q).eval 1 = 0 := by
    intro d hd
    rw [hev d]
    have h := hJ d (by omega)
    rw [if_neg (by omega)] at h
    exact (mul_eq_zero.mp h).resolve_left (hfac d (by omega))
  have hnot : ¬ ∀ d < m + 1, (hasseDeriv d q).eval 1 = 0 := by
    intro h
    have h1 := h m (by omega)
    rw [hev m] at h1
    have h2 := hJ m le_rfl
    rw [if_pos rfl, h1, mul_zero] at h2
    exact (neg_ne_zero.mpr one_ne_zero) h2.symm
  refine ⟨?_, ?_⟩
  · show npoly ((p - 1) / 2) ∣ q
    rw [← hm, hnpoly]
    exact (hD m).mpr hzero
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly] at hn'
    show n ≤ (p - 1) / 2
    rw [← hm]
    by_contra hlt
    have h3 : (X - 1 : (ZMod p)[X]) ^ (m + 1) ∣ q := dvd_trans (pow_dvd_pow _ (by omega)) hn'
    exact hnot ((hD (m + 1)).mp h3)
