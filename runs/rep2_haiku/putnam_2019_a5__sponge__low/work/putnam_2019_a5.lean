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
  have := Fact.mk pprime
  have : NeZero p := ⟨pprime.ne_zero⟩
  obtain ⟨t, ht⟩ := podd
  obtain ⟨m, hm⟩ : ∃ m, (p - 1) / 2 = m := ⟨_, rfl⟩
  have hp2 : p = 2 * m + 1 := by omega
  have hm1 : 1 ≤ m := by have := pprime.two_le; omega
  show IsGreatest {n | npoly n ∣ q} ((p - 1) / 2)
  rw [hm]
  -- q has degree < p
  have hdeg : q.natDegree < p := by
    have : q.natDegree ≤ p - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hq N, ha0.2 N (by omega)]
    have := pprime.two_le
    omega
  -- a i = i^m on range p
  have hcast : ∀ i < p, a i = ((i : ZMod p)) ^ m := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [Nat.cast_zero]
      rw [ha0.1, zero_pow (by omega)]
    · have := haother ⟨i, Set.mem_Icc.mpr ⟨hpos, by omega⟩⟩
      simp only at this
      rw [this, ZMod.natCast_mod, Nat.cast_pow, hm]
  -- Taylor coefficients at 1
  have hT : ∀ j : ℕ, (Polynomial.taylor 1 q).coeff j
      = ∑ i ∈ Finset.range p, a i * ((i.choose j : ℕ) : ZMod p) := by
    intro j
    conv_lhs => rw [Polynomial.as_sum_range' q p hdeg]
    rw [map_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.taylor_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, hq i]
    simp [mul_comm]
  -- divisibility via Taylor coefficients
  have hX : Polynomial.taylor (1 : ZMod p) (Polynomial.X - 1) = Polynomial.X := by
    simp [Polynomial.taylor_apply]
  have hsub : ∀ n : ℕ, Polynomial.taylor (1 : ZMod p) ((Polynomial.X - 1) ^ n) = Polynomial.X ^ n := by
    intro n
    induction n with
    | zero => simp [Polynomial.taylor_apply]
    | succ k ih => rw [pow_succ, Polynomial.taylor_mul, ih, hX, pow_succ]
  have hpowX : ∀ (r : ZMod p) (n : ℕ), Polynomial.taylor r (Polynomial.X ^ n) = (Polynomial.X + Polynomial.C r) ^ n := by
    intro r n
    induction n with
    | zero => simp [Polynomial.taylor_apply]
    | succ k ih => rw [pow_succ, Polynomial.taylor_mul, ih, Polynomial.taylor_X, pow_succ]
  have key : ∀ (r : ZMod p) (f g : Polynomial (ZMod p)), f ∣ g → Polynomial.taylor r f ∣ Polynomial.taylor r g := by
    rintro r f g ⟨c, rfl⟩
    rw [Polynomial.taylor_mul]
    exact dvd_mul_right _ _
  have hdiv : ∀ n : ℕ, (Polynomial.X - 1) ^ n ∣ q ↔ ∀ j < n, (Polynomial.taylor 1 q).coeff j = 0 := by
    intro n
    constructor
    · intro h
      have h2 := key 1 _ _ h
      rw [hsub] at h2
      exact Polynomial.X_pow_dvd_iff.mp h2
    · intro h
      have h2 : Polynomial.X ^ n ∣ Polynomial.taylor 1 q := Polynomial.X_pow_dvd_iff.mpr h
      have h3 := key (-1) _ _ h2
      have hXn : Polynomial.taylor (-1 : ZMod p) (Polynomial.X ^ n) = (Polynomial.X - 1) ^ n := by
        rw [hpowX]
        simp [sub_eq_add_neg]
      rw [hXn, Polynomial.taylor_taylor, show (-1 : ZMod p) + 1 = 0 by ring, Polynomial.taylor_zero] at h3
      exact h3
  -- character sums
  have hconv : ∀ f : ZMod p → ZMod p, ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
    intro f
    have hinj : Set.InjOn (fun i : ℕ => (i : ZMod p)) (Finset.range p : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      have := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
      rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
    have himg : (Finset.range p).image (fun i : ℕ => (i : ZMod p)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
    rw [← Finset.sum_image (f := f) hinj, himg]
  have hS : ∀ e : ℕ, e < p - 1 → ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ e = 0 := by
    intro e he
    rw [hconv (fun x => x ^ e)]
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) e (by rw [ZMod.card]; exact he)
  have hSlast : ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ (p - 1) = -1 := by
    have hpt : ∀ x : ZMod p, x ^ (p - 1) = if x = 0 then 0 else 1 := by
      intro x
      by_cases hx : x = 0
      · subst hx
        rw [if_pos rfl, zero_pow (by omega)]
      · rw [if_neg hx, ZMod.pow_card_sub_one_eq_one hx]
    rw [hconv (fun x => x ^ (p - 1)), Finset.sum_congr rfl (fun x _ => hpt x)]
    simp [Finset.sum_ite, Finset.filter_ne', ZMod.card, Finset.card_erase_of_mem]
    rw [Nat.cast_sub (by have := pprime.two_le; omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hfac : ∀ j < p, ((j.factorial : ℕ) : ZMod p) ≠ 0 := by
    intro j hj h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := (Nat.Prime.dvd_factorial pprime).mp h0
    omega
  have hcj : ∀ i j : ℕ, ((i.choose j : ℕ) : ZMod p) * ((j.factorial : ℕ) : ZMod p)
      = (descPochhammer (ZMod p) j).eval (i : ZMod p) := by
    intro i j
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hmain : ∀ j : ℕ, (Polynomial.taylor 1 q).coeff j * ((j.factorial : ℕ) : ZMod p)
      = ∑ d ∈ Finset.range (j + 1), (descPochhammer (ZMod p) j).coeff d
          * ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ (m + d) := by
    intro j
    rw [hT j, Finset.sum_mul]
    have step1 : ∀ i ∈ Finset.range p, a i * ((i.choose j : ℕ) : ZMod p) * ((j.factorial : ℕ) : ZMod p)
        = (i : ZMod p) ^ m * (descPochhammer (ZMod p) j).eval (i : ZMod p) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hcast i hi, ← hcj i j]
      ring
    rw [Finset.sum_congr rfl step1]
    simp only [Polynomial.eval_eq_sum_range, descPochhammer_natDegree]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add]
    ring
  have hlow : ∀ j < m, (Polynomial.taylor 1 q).coeff j = 0 := by
    intro j hj
    have h := hmain j
    have hz : ∑ d ∈ Finset.range (j + 1), (descPochhammer (ZMod p) j).coeff d
        * ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ (m + d) = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [Finset.mem_range] at hd
      rw [hS (m + d) (by omega), mul_zero]
    rw [hz] at h
    exact (mul_eq_zero.mp h).resolve_right (hfac j (by omega))
  have hhigh : (Polynomial.taylor 1 q).coeff m ≠ 0 := by
    intro h0
    have h := hmain m
    rw [h0, zero_mul, Finset.sum_range_succ] at h
    have hz : ∑ d ∈ Finset.range m, (descPochhammer (ZMod p) m).coeff d
        * ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ (m + d) = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [Finset.mem_range] at hd
      rw [hS (m + d) (by omega), mul_zero]
    have hPc : (descPochhammer (ZMod p) m).coeff m = 1 := by
      have := (monic_descPochhammer (ZMod p) m).coeff_natDegree
      rwa [descPochhammer_natDegree] at this
    have hS2 : ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ (m + m) = -1 := by
      rw [show m + m = p - 1 by omega]
      exact hSlast
    rw [hz, zero_add, hPc, hS2, one_mul] at h
    exact (neg_ne_zero.mpr one_ne_zero) h.symm
  constructor
  · show npoly m ∣ q
    rw [hnpoly, hdiv]
    intro j hj
    exact hlow j hj
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly, hdiv] at hn'
    by_contra hlt
    push Not at hlt
    exact hhigh (hn' m hlt)
