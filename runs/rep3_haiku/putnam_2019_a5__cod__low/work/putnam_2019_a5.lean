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
  (
  have := Fact.mk pprime
  obtain ⟨hp0, hpk⟩ := ha0
  have hp3 : 3 ≤ p := by
    have := pprime.two_le
    obtain ⟨k, hk⟩ := podd
    omega
  have hpe : p - 1 = 2 * ((p - 1) / 2) := by
    obtain ⟨k, hk⟩ := podd
    omega
  set e := (p - 1) / 2 with he
  have he1 : 1 ≤ e := by omega
  have hsum_lt : ∀ i, i < p - 1 → ∑ x : ZMod p, x ^ i = 0 := by
    intro i hi
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by rw [ZMod.card]; exact hi)
  have hsum_top : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
    have h1 : ∀ x : ZMod p, x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
      intro x
      by_cases hx : x = 0
      · subst hx
        rw [if_pos rfl, zero_pow (by omega)]
        ring
      · rw [if_neg hx, sub_zero, ZMod.pow_card_sub_one_eq_one hx]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib]
    simp [ZMod.card]
  have hreindex : ∀ f : ZMod p → ZMod p, ∑ k ∈ Finset.range p, f (k : ZMod p) = ∑ x : ZMod p, f x := by
    intro f
    have himg : (Finset.range p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_image]
      refine ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    rw [← Finset.sum_image (f := f), himg]
    intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' := (ZMod.natCast_eq_natCast_iff' a b p).mp h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'
  have ha : ∀ k ∈ Finset.range p, a k = (k : ZMod p) ^ e := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hp0, zero_pow (show e ≠ 0 by omega)]
    · have hkp : k < p := Finset.mem_range.mp hk
      have := haother ⟨k, by simp only [Set.mem_Icc]; omega⟩
      simp only at this
      rw [this, ← Nat.cast_pow, ZMod.natCast_mod]
  set S : ℕ → ZMod p := fun j => ∑ x : ZMod p, x ^ e * (descPochhammer (ZMod p) j).eval x with hS
  have hSlow : ∀ j, j < e → S j = 0 := by
    intro j hj
    simp only [hS]
    have hdeg : (descPochhammer (ZMod p) j).natDegree < j + 1 := by
      rw [descPochhammer_natDegree]; omega
    simp only [eval_eq_sum_range' hdeg, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have : ∑ x : ZMod p, x ^ e * ((descPochhammer (ZMod p) j).coeff i * x ^ i)
        = (descPochhammer (ZMod p) j).coeff i * ∑ x : ZMod p, x ^ (e + i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_add]; ring
    rw [this, hsum_lt (e + i) (by omega), mul_zero]
  have hSe : S e = -1 := by
    simp only [hS]
    have hdeg : (descPochhammer (ZMod p) e).natDegree = e := descPochhammer_natDegree _ _
    have hmon := monic_descPochhammer (ZMod p) e
    have hlead : (descPochhammer (ZMod p) e).coeff e = 1 := by
      have := hmon.coeff_natDegree
      rwa [hdeg] at this
    have hdeg' : (descPochhammer (ZMod p) e).natDegree < e + 1 := by omega
    have hpt : ∀ x : ZMod p, x ^ e * (descPochhammer (ZMod p) e).eval x
        = (∑ i ∈ Finset.range e, (descPochhammer (ZMod p) e).coeff i * x ^ (e + i)) + x ^ (p - 1) := by
      intro x
      rw [eval_eq_sum_range' hdeg', Finset.sum_range_succ, hlead, one_mul, hpe]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [pow_add]; ring
      · rw [← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, hsum_top]
    have h0 : ∑ x : ZMod p, ∑ i ∈ Finset.range e, (descPochhammer (ZMod p) e).coeff i * x ^ (e + i) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      rw [← Finset.mul_sum, hsum_lt (e + i) (by omega), mul_zero]
    rw [h0, zero_add]
  have hdeg : q.natDegree ≤ p - 1 :=
    natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => by rw [hq]; exact hpk N (by omega))
  have hq' : q = ∑ k ∈ Finset.range p, C (a k) * X ^ k := by
    conv_lhs => rw [as_sum_range' q p (by omega)]
    apply Finset.sum_congr rfl
    intro k _
    rw [hq, C_mul_X_pow_eq_monomial]
  have hT : ∀ j, j ≤ e → (derivative^[j] q).eval 1 = S j := by
    intro j hj
    rw [hq', iterate_derivative_sum, eval_finsetSum]
    have step : ∀ k ∈ Finset.range p, (derivative^[j] (C (a k) * X ^ k)).eval 1
        = (k : ZMod p) ^ e * ((descPochhammer (ZMod p) j).eval (k : ZMod p)) := by
      intro k hk
      rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul, descPochhammer_eval_eq_descFactorial]
      simp only [eval_mul, eval_C, eval_smul, eval_pow, eval_X, one_pow, smul_eq_mul]
      rw [ha k hk]
      simp
    rw [Finset.sum_congr rfl step, hreindex (fun x => x ^ e * (descPochhammer (ZMod p) j).eval x)]
  have hT0 : ∀ j < e, (derivative^[j] q).eval 1 = 0 := fun j hj => by
    rw [hT j hj.le, hSlow j hj]
  have hTe : (derivative^[e] q).eval 1 = -1 := by
    rw [hT e le_rfl, hSe]
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hTe
    simp at hTe
  have hfac : ∀ n < p, ((n.factorial : ℕ) : ZMod p) ≠ 0 := by
    intro n hn h
    rw [ZMod.natCast_eq_zero_iff] at h
    · have := (Nat.Prime.dvd_factorial pprime).mp h
      omega
  have hr : rootMultiplicity 1 q = e := by
    apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      have hl := (lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
        hq0 (mem_nonZeroDivisors_of_ne_zero (hfac e (by omega)))).mp hlt
      have := hl e le_rfl
      rw [IsRoot.def, hTe] at this
      norm_num at this
    · have hl := (lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors
        hq0 (mem_nonZeroDivisors_of_ne_zero (hfac (e - 1) (by omega)))).mpr (fun m hm => by
          show (derivative^[m] q).eval 1 = 0
          exact hT0 m (by omega))
      omega
  have hdivE : (X - C 1) ^ e ∣ q := (le_rootMultiplicity_iff hq0).mp (by rw [hr])
  simp only [map_one] at hdivE
  constructor
  · show npoly e ∣ q
    rw [hnpoly]; exact hdivE
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly] at hn'
    have : n ≤ rootMultiplicity 1 q := by
      apply (le_rootMultiplicity_iff hq0).mpr
      simpa using hn'
    rw [hr] at this
    exact this)
