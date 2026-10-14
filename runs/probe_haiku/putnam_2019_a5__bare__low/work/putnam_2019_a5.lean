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
  have := Fact.mk pprime
  obtain ⟨k, hk⟩ := podd
  have hp3 : 3 ≤ p := by
    have := pprime.two_le
    omega
  set m := (p - 1) / 2 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hm2 : m + m = p - 1 := by omega
  have ha : ∀ i < p, a i = (i : ZMod p) ^ m := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [ha0.1, Nat.cast_zero, zero_pow (show m ≠ 0 by omega)]
    · have h := haother ⟨i, by simp; omega⟩
      simp only at h
      rw [h, ZMod.natCast_mod, Nat.cast_pow]
  have hqsum : q = ∑ i ∈ Finset.range p, Polynomial.C (a i) * Polynomial.X ^ i := by
    ext n
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [hq n]
    by_cases hn : n < p
    · simp [hn]
    · have : a n = 0 := ha0.2 n (by omega)
      simp [this, hn]
  have htc : ∀ d, (Polynomial.taylor 1 q).coeff d
      = ∑ i ∈ Finset.range p, a i * ((i.choose d : ℕ) : ZMod p) := by
    intro d
    rw [hqsum, map_sum, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, map_one, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]
  have hcoef : ∀ d, (Polynomial.taylor 1 q).coeff d
      = ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose d : ℕ) : ZMod p) := by
    intro d
    rw [htc]
    exact Finset.sum_congr rfl (fun i hi => by rw [ha i (Finset.mem_range.mp hi)])
  have hsumuniv : ∀ e : ℕ, ∑ i ∈ Finset.range p, ((i : ℕ) : ZMod p) ^ e = ∑ x : ZMod p, x ^ e := by
    intro e
    have himg : (Finset.range p).image (fun i : ℕ => (i : ZMod p)) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      rw [Finset.mem_image]
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    rw [← himg, Finset.sum_image]
    intro i hi j hj hij
    have h1 := Finset.mem_range.mp hi
    have h2 := Finset.mem_range.mp hj
    have := (ZMod.natCast_eq_natCast_iff' i j p).mp hij
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  have hS0 : ∀ e, e < p - 1 → ∑ i ∈ Finset.range p, ((i : ℕ) : ZMod p) ^ e = 0 := by
    intro e h2
    rw [hsumuniv]
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) e (by rw [ZMod.card]; exact h2)
  have hSp : ∑ i ∈ Finset.range p, ((i : ℕ) : ZMod p) ^ (p - 1) = -1 := by
    rw [hsumuniv]
    have h1 : ∀ x : ZMod p, x ^ (p-1) = if x = 0 then 0 else 1 := by
      intro x
      by_cases hx : x = 0
      · simp [hx]; omega
      · simp [hx, ZMod.pow_card_sub_one_eq_one hx]
    have hc : (Finset.univ.filter (fun x : ZMod p => ¬ x = 0)).card = p - 1 := by
      rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hc, Nat.cast_sub (Nat.Prime.one_le pprime), ZMod.natCast_self]
    simp
  have hL : ∀ P : Polynomial (ZMod p), ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * P.eval (i : ZMod p)
      = ∑ l ∈ Finset.range (P.natDegree + 1), P.coeff l * ∑ i ∈ Finset.range p, (i : ZMod p) ^ (m + l) := by
    intro P
    simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => by ring))
  have hT : ∀ d, (d.factorial : ZMod p) * ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose d : ℕ) : ZMod p)
      = ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * (descPochhammer (ZMod p) d).eval (i : ZMod p) := by
    intro d
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hTz : ∀ d, d < m → ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose d : ℕ) : ZMod p) = 0 := by
    intro d hd
    have hfac : (d.factorial : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial pprime]
      omega
    have h : (d.factorial : ZMod p) * ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose d : ℕ) : ZMod p) = 0 := by
      rw [hT, hL, descPochhammer_natDegree]
      apply Finset.sum_eq_zero
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [hS0 (m + l) (by omega), mul_zero]
    exact (mul_eq_zero.mp h).resolve_left hfac
  have hTm : ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose m : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have h1 : (m.factorial : ZMod p) * ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose m : ℕ) : ZMod p) = 0 := by
      rw [h, mul_zero]
    have hmon : (descPochhammer (ZMod p) m).coeff m = 1 := by
      have := (monic_descPochhammer (ZMod p) m).coeff_natDegree
      rwa [descPochhammer_natDegree] at this
    have hz : ∑ l ∈ Finset.range m, (descPochhammer (ZMod p) m).coeff l
        * ∑ i ∈ Finset.range p, (i : ZMod p) ^ (m + l) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [hS0 (m + l) (by omega), mul_zero]
    rw [hT, hL, descPochhammer_natDegree, Finset.sum_range_succ, hz, zero_add, hmon, hm2, hSp,
      one_mul] at h1
    exact one_ne_zero (neg_eq_zero.mp h1)
  have key : ∀ n, (Polynomial.X - 1 : Polynomial (ZMod p)) ^ n ∣ q
      ↔ ∀ d < n, ∑ i ∈ Finset.range p, (i : ZMod p) ^ m * ((i.choose d : ℕ) : ZMod p) = 0 := by
    intro n
    have e : (Polynomial.X - 1 : Polynomial (ZMod p)) = Polynomial.X - Polynomial.C 1 := by simp
    rw [e, Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply, Polynomial.X_pow_dvd_iff]
    simp only [hcoef]
  refine ⟨?_, ?_⟩
  · have hmem : npoly m ∣ q := by
      rw [hnpoly, key]
      intro d hd
      exact hTz d hd
    exact hmem
  · intro n hn
    have hn' : npoly n ∣ q := hn
    rw [hnpoly, key] at hn'
    by_contra hc
    have hc' : m < n := by
      have hc2 : ¬ n ≤ m := hc
      omega
    exact hTm (hn' m (by omega))
