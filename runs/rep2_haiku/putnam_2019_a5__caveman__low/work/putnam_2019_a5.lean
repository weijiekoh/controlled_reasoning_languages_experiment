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
  haveI : Fact p.Prime := ⟨pprime⟩
  obtain ⟨r, hr⟩ := podd
  have hp2 := pprime.two_le
  obtain ⟨m, hmdef⟩ : ∃ m, m = (p - 1) / 2 := ⟨_, rfl⟩
  have hpm : p = 2 * m + 1 := by omega
  have hm1 : 1 ≤ m := by omega
  show IsGreatest {n | npoly n ∣ q} ((p - 1) / 2)
  rw [← hmdef]
  have hqsum : q = ∑ k ∈ Finset.range p, Polynomial.C ((k : ZMod p) ^ m) * Polynomial.X ^ k := by
    ext n
    rw [hq n, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_range]
    by_cases hn : n < p
    · rw [if_pos hn]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simp [ha0.1, zero_pow (by omega : m ≠ 0)]
      · have hmem : n ∈ Set.Icc 1 (p - 1) := ⟨hpos, by omega⟩
        have h := haother ⟨n, hmem⟩
        simp only at h
        rw [h, ZMod.natCast_mod, Nat.cast_pow, hmdef]
    · rw [if_neg hn, ha0.2 n (by omega)]
  have hsum_conv : ∀ f : ZMod p → ZMod p,
      ∑ k ∈ Finset.range p, f (k : ZMod p) = ∑ x : ZMod p, f x := by
    intro f
    refine Finset.sum_bij (fun k _ => (k : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_
      (fun _ _ => rfl)
    · intro a ha b hb h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (Finset.mem_range.1 ha),
        Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at h
      exact h
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
  have hS : ∀ e, e < m → ∑ x : ZMod p, x ^ (m + e) = 0 := by
    intro e he
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  have hTop : ∑ x : ZMod p, x ^ (m + m) = -1 := by
    rw [show m + m = p - 1 by omega]
    have key : ∀ x : ZMod p, x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
      intro x
      by_cases hx : x = 0
      · subst hx; simp [zero_pow (by omega : p - 1 ≠ 0)]
      · simp [hx, ZMod.pow_card_sub_one_eq_one hx]
    simp only [key, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [ZMod.card]
  have hG : ∀ P : Polynomial (ZMod p), P.natDegree < m + 1 →
      ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * P.eval (k : ZMod p) = - P.coeff m := by
    intro P hP
    have hk : ∀ k : ℕ, (k : ZMod p) ^ m * P.eval (k : ZMod p)
        = ∑ e ∈ Finset.range (m + 1), P.coeff e * (k : ZMod p) ^ (m + e) := by
      intro k
      rw [Polynomial.eval_eq_sum_range' hP, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_comm]
    have hin : ∀ e ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range p, P.coeff e * (k : ZMod p) ^ (m + e)
          = P.coeff e * ∑ x : ZMod p, x ^ (m + e) := by
      intro e _
      rw [Finset.mul_sum]
      exact hsum_conv (fun x => P.coeff e * x ^ (m + e))
    rw [Finset.sum_congr rfl hin, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun e he => by
      rw [hS e (Finset.mem_range.1 he), mul_zero])]
    rw [hTop]
    simp
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ZMod p, ∀ j, c j = ∑ k ∈ Finset.range p,
      (k : ZMod p) ^ m * ((k.choose j : ℕ) : ZMod p) := ⟨_, fun _ => rfl⟩
  have hid : ∀ j, ∑ k ∈ Finset.range p, (k : ZMod p) ^ m *
      (descPochhammer (ZMod p) j).eval (k : ZMod p) = (j.factorial : ZMod p) * c j := by
    intro j
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hfac : ∀ j, j < m → (j.factorial : ZMod p) ≠ 0 := by
    intro j hj h
    have hd : p ∣ j.factorial := (ZMod.natCast_eq_zero_iff _ _).1 h
    have := (Nat.Prime.dvd_factorial pprime).1 hd
    omega
  have hcj : ∀ j, j < m → c j = 0 := by
    intro j hj
    have h1 := hG (descPochhammer (ZMod p) j) (by rw [descPochhammer_natDegree]; omega)
    have hcoeff : (descPochhammer (ZMod p) j).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; omega)
    rw [hcoeff, neg_zero] at h1
    have h2 := hid j
    rw [h1] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (hfac j hj)
  have hcm : c m ≠ 0 := by
    intro hc0
    have h1 := hG (descPochhammer (ZMod p) m) (by rw [descPochhammer_natDegree]; omega)
    have hone : (descPochhammer (ZMod p) m).coeff m = 1 := by
      have := (monic_descPochhammer (ZMod p) m).coeff_natDegree
      rwa [descPochhammer_natDegree] at this
    rw [hone] at h1
    have h2 := hid m
    rw [h1, hc0, mul_zero] at h2
    exact one_ne_zero (neg_eq_zero.mp h2)
  have hcoef : ∀ j, (Polynomial.taylor 1 q).coeff j = c j := by
    intro j
    rw [Polynomial.taylor_apply, hqsum, Polynomial.sum_comp, Polynomial.finsetSum_coeff, hc]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, map_one]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]
  have hL : ∀ n, (Polynomial.X - 1) ^ n ∣ q ↔ Polynomial.X ^ n ∣ Polynomial.taylor 1 q := by
    intro n
    have hX : Polynomial.taylor (1 : ZMod p) (Polynomial.X - 1) = Polynomial.X := by
      rw [Polynomial.taylor_apply]
      simp
    have hq' : q = (Polynomial.taylor 1 q).comp (Polynomial.X - 1) := by
      rw [Polynomial.taylor_apply, Polynomial.comp_assoc]
      simp
    constructor
    · rintro ⟨s, hs⟩
      rw [hs, Polynomial.taylor_mul, Polynomial.taylor_pow, hX]
      exact dvd_mul_right _ _
    · rintro ⟨s, hs⟩
      have hq2 : q = (Polynomial.X ^ n * s).comp (Polynomial.X - 1) := by
        rw [← hs]; exact hq'
      rw [hq2, Polynomial.mul_comp, Polynomial.X_pow_comp]
      exact dvd_mul_right _ _
  have hdiv : ∀ n, (Polynomial.X - 1) ^ n ∣ q ↔ ∀ j < n, c j = 0 := by
    intro n
    rw [hL, Polynomial.X_pow_dvd_iff]
    simp only [hcoef]
  constructor
  · show npoly m ∣ q
    rw [hnpoly, hdiv]
    exact fun j hj => hcj j hj
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly, hdiv] at hn'
    by_contra h
    push_neg at h
    exact hcm (hn' m h)
