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
  IsGreatest {n | npoly n ∣ q} (putnam_2019_a5_solution p) :=
by
  open Polynomial in
    have := Fact.mk pprime
    have : NeZero p := ⟨pprime.ne_zero⟩
    show IsGreatest {n | npoly n ∣ q} ((p - 1) / 2)
    obtain ⟨t, ht⟩ := podd
    obtain ⟨m, hm⟩ : ∃ m, m = (p - 1) / 2 := ⟨_, rfl⟩
    rw [← hm]
    have hpm : p = 2 * m + 1 := by omega
    have hm1 : 1 ≤ m := by have := pprime.two_le; omega
    have hmp : m < p := by omega
    -- a k = k^m on range p
    have ha : ∀ k < p, a k = (k : ZMod p) ^ m := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [ha0.1, Nat.cast_zero, zero_pow (by omega : m ≠ 0)]
      · have h := haother ⟨k, Set.mem_Icc.mpr ⟨hk0, by omega⟩⟩
        simp only at h
        rw [h, ZMod.natCast_mod, hm, Nat.cast_pow]
    -- q as a sum of monomials
    have hq' : q = ∑ k ∈ Finset.range p, monomial k ((k : ZMod p) ^ m) := by
      ext n
      rw [finsetSum_coeff]
      simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, hq]
      split_ifs with h
      · exact ha n h
      · exact ha0.2 n (by omega)
    -- Hasse derivative evaluated at 1
    have hc : ∀ d, eval 1 (hasseDeriv d q) = ∑ k ∈ Finset.range p, ((k.choose d : ℕ) : ZMod p) * (k : ZMod p) ^ m := by
      intro d
      rw [hq', map_sum, eval_finset_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hasseDeriv_monomial, eval_monomial, one_pow, mul_one]
    -- power sums over ZMod p
    have hsum_range : ∀ f : ZMod p → ZMod p, ∑ k ∈ Finset.range p, f (k : ZMod p) = ∑ x, f x := by
      intro f
      have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (Finset.range p : Set ℕ) := by
        intro a ha' b hb' h
        simp only [Finset.coe_range, Set.mem_Iio] at ha' hb'
        have h' := (ZMod.natCast_eq_natCast_iff' a b p).mp h
        rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h'
      have himg : (Finset.range p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ := by
        ext x
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
        exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
      calc ∑ k ∈ Finset.range p, f (k : ZMod p)
          = ∑ x ∈ (Finset.range p).image (fun k : ℕ => (k : ZMod p)), f x :=
            (Finset.sum_image (fun a ha' b hb' h => hinj ha' hb' h)).symm
        _ = ∑ x, f x := by rw [himg]
    have hS : ∀ e, e < p - 1 → ∑ k ∈ Finset.range p, (k : ZMod p) ^ e = 0 := by
      intro e he
      rw [hsum_range (fun x => x ^ e)]
      have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) (i := e) (by rw [ZMod.card]; exact he)
      exact this
    have hSm : ∑ k ∈ Finset.range p, (k : ZMod p) ^ (p - 1) = -1 := by
      rw [hsum_range (fun x => x ^ (p - 1))]
      have hx : ∀ x : ZMod p, x ^ (p - 1) = 1 - if x = 0 then 1 else 0 := by
        intro x
        by_cases hx0 : x = 0
        · subst hx0; rw [zero_pow (by omega)]; simp
        · rw [ZMod.pow_card_sub_one_eq_one hx0]; simp [hx0]
      simp only [hx]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp [ZMod.card]
    -- sum of polynomial over the field
    have hgsum : ∀ g : (ZMod p)[X], g.natDegree < p →
        ∑ k ∈ Finset.range p, eval (k : ZMod p) g = -g.coeff (p - 1) := by
      intro g hg
      simp_rw [eval_eq_sum_range' hg]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_eq_single (p - 1)]
      · rw [hSm, mul_neg_one]
      · intro e he hne
        rw [hS e (by simp only [Finset.mem_range] at he; omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    have hfac_ne : ∀ d, d < p → (d.factorial : ZMod p) ≠ 0 := by
      intro d hd h
      have h2 := (ZMod.natCast_eq_zero_iff _ p).mp h
      rw [pprime.dvd_factorial] at h2
      omega
    -- key identity
    have hfac : ∀ d, d ≤ m →
        (d.factorial : ZMod p) * eval 1 (hasseDeriv d q)
          = -((X ^ m * descPochhammer (ZMod p) d).coeff (p - 1)) := by
      intro d hd
      rw [hc d, Finset.mul_sum]
      have hterm : ∀ k ∈ Finset.range p,
          (d.factorial : ZMod p) * (((k.choose d : ℕ) : ZMod p) * (k : ZMod p) ^ m)
            = eval (k : ZMod p) (X ^ m * descPochhammer (ZMod p) d) := by
        intro k _
        rw [eval_mul, eval_pow, eval_X, descPochhammer_eval_eq_descFactorial,
          Nat.descFactorial_eq_factorial_mul_choose]
        push_cast; ring
      rw [Finset.sum_congr rfl hterm]
      have hdeg : (X ^ m * descPochhammer (ZMod p) d).natDegree < p := by
        have h1 := natDegree_mul_le (p := (X ^ m : (ZMod p)[X])) (q := descPochhammer (ZMod p) d)
        rw [natDegree_X_pow, descPochhammer_natDegree] at h1
        omega
      exact hgsum _ hdeg
    have hcoeff : ∀ d, d ≤ m →
        (X ^ m * descPochhammer (ZMod p) d).coeff (p - 1) = if d = m then 1 else 0 := by
      intro d hd
      rw [coeff_X_pow_mul', if_pos (by omega : m ≤ p - 1)]
      have hp1 : p - 1 - m = m := by omega
      rw [hp1]
      split_ifs with hdm
      · subst hdm
        have hmon := (monic_descPochhammer (ZMod p) d)
        have := hmon.coeff_natDegree
        rwa [descPochhammer_natDegree] at this
      · apply coeff_eq_zero_of_natDegree_lt
        rw [descPochhammer_natDegree]; omega
    -- divisibility criterion
    have key : ∀ n, (X - 1 : (ZMod p)[X]) ^ n ∣ q ↔ ∀ d < n, eval 1 (hasseDeriv d q) = 0 := by
      intro n
      rw [show (X - 1 : (ZMod p)[X]) = X - C 1 by simp, X_sub_C_pow_dvd_iff, ← taylor_apply,
        X_pow_dvd_iff]
      simp only [taylor_coeff]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, hnpoly]
      rw [key]
      intro d hd
      have h := hfac d (by omega)
      rw [hcoeff d (by omega), if_neg (by omega), neg_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (hfac_ne d (by omega))
    · intro n hn
      simp only [Set.mem_setOf_eq, hnpoly] at hn
      by_contra hlt
      push_neg at hlt
      have h1 : (X - 1 : (ZMod p)[X]) ^ (m + 1) ∣ q := (pow_dvd_pow _ (by omega : m + 1 ≤ n)).trans hn
      rw [key] at h1
      have h0 := h1 m (by omega)
      have h2 := hfac m le_rfl
      rw [hcoeff m le_rfl, if_pos rfl, h0, mul_zero] at h2
      have h3 : (1 : ZMod p) = 0 := by
        have := congrArg (fun z => -z) h2
        simpa using this.symm
      exact one_ne_zero h3
