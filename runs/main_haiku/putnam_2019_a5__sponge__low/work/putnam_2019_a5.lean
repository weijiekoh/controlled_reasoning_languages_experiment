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
  classical
  haveI : Fact p.Prime := ⟨pprime⟩
  show IsGreatest {n | npoly n ∣ q} ((p - 1) / 2)
  obtain ⟨m, hm⟩ : ∃ m, (p - 1) / 2 = m := ⟨_, rfl⟩
  rw [hm]
  obtain ⟨r, hr⟩ := podd
  have hp : p = 2 * m + 1 := by have := pprime.two_le; omega
  have hm1 : m ≠ 0 := by have := pprime.two_le; omega
  have hpm : p - 1 = m + m := by omega
  have hpne : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hA : ∀ k < p, a k = (k : ZMod p) ^ m := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [ha0.1]; simp [hm1]
    · have := haother ⟨k, Set.mem_Icc.mpr ⟨hpos, by omega⟩⟩
      rw [this, hm]
      simp
  have hq' : q = ∑ k ∈ Finset.range p, Polynomial.C (a k) * Polynomial.X ^ k := by
    ext n
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [hq n]
    by_cases hn : n < p
    · rw [Finset.sum_ite_eq]; simp [hn]
    · have h0 : a n = 0 := ha0.2 n (by omega)
      rw [h0]; simp [hn]
  have hcoef : ∀ j, (Polynomial.taylor 1 q).coeff j
      = ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * ((k.choose j : ℕ) : ZMod p) := by
    intro j
    rw [Polynomial.taylor_apply, hq', Polynomial.sum_comp]
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    rw [Polynomial.coeff_C_mul]
    simp only [map_one]
    rw [Polynomial.coeff_X_add_one_pow, hA k hk]
  have hS : ∀ i < p - 1, ∑ x : ZMod p, x ^ i = 0 := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp [Finset.sum_const, Finset.card_univ, ZMod.card, hpne]
    · exact FiniteField.sum_pow_lt_card_sub_one _ i (by rw [ZMod.card]; exact hi)
  have hpow : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
    have h1 : ∀ x : ZMod p, x ^ (p - 1) = 1 - (if x = 0 then 1 else 0) := by
      intro x
      by_cases hx : x = 0
      · subst hx; simp [zero_pow (show p - 1 ≠ 0 by omega)]
      · rw [ZMod.pow_card_sub_one_eq_one hx]; simp [hx]
    simp_rw [h1]
    simp [Finset.sum_sub_distrib, Finset.card_univ, ZMod.card, hpne]
  have hsum : ∀ P : Polynomial (ZMod p), P.natDegree < p →
      ∑ x : ZMod p, P.eval x = -P.coeff (p - 1) := by
    intro P hP
    simp_rw [Polynomial.eval_eq_sum_range' hP]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have h := Finset.sum_range_succ (fun i => P.coeff i * ∑ x : ZMod p, x ^ i) (p - 1)
    rw [show p - 1 + 1 = p by omega] at h
    rw [h, Finset.sum_eq_zero (fun i hi => by
      rw [hS i (by simp at hi; omega), mul_zero]), zero_add, hpow, mul_neg_one]
  have hbij : ∀ g : ZMod p → ZMod p,
      ∑ k ∈ Finset.range p, g (k : ZMod p) = ∑ x : ZMod p, g x := by
    intro g
    symm
    refine Finset.sum_nbij' (fun x : ZMod p => x.val) (fun k : ℕ => (k : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
    · intro a _; rw [ZMod.natCast_zmod_val]
  have hfac : ∀ j < p, ((j.factorial : ℕ) : ZMod p) ≠ 0 := by
    intro j hj h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := (Nat.Prime.dvd_factorial pprime).mp h0
    omega
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ → Polynomial (ZMod p),
      ∀ j, h j = Polynomial.C (((j.factorial : ℕ) : ZMod p))⁻¹ * descPochhammer (ZMod p) j :=
    ⟨_, fun j => rfl⟩
  have hdeg : ∀ j, (h j).natDegree ≤ j := by
    intro j
    rw [hhdef]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (descPochhammer_natDegree (ZMod p) j).le
  have hev : ∀ j < p, ∀ k : ℕ, (h j).eval (k : ZMod p) = ((k.choose j : ℕ) : ZMod p) := by
    intro j hj k
    rw [hhdef, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
      inv_mul_cancel₀ (hfac j hj), one_mul]
  have hSj : ∀ j ≤ m, ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * ((k.choose j : ℕ) : ZMod p)
      = -(h j).coeff m := by
    intro j hj
    have hdegP : (h j * Polynomial.X ^ m).natDegree < p := by
      have := Polynomial.natDegree_mul_le (p := h j) (q := Polynomial.X ^ m)
      rw [Polynomial.natDegree_X_pow] at this
      have := hdeg j
      omega
    calc ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * ((k.choose j : ℕ) : ZMod p)
        = ∑ k ∈ Finset.range p, (h j * Polynomial.X ^ m).eval (k : ZMod p) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hev j (by omega) k]
          ring
      _ = ∑ x : ZMod p, (h j * Polynomial.X ^ m).eval x :=
          hbij (fun x => (h j * Polynomial.X ^ m).eval x)
      _ = -(h j * Polynomial.X ^ m).coeff (p - 1) := hsum _ hdegP
      _ = -(h j).coeff m := by rw [hpm, Polynomial.coeff_mul_X_pow]
  have hSlt : ∀ j < m, ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * ((k.choose j : ℕ) : ZMod p) = 0 := by
    intro j hj
    rw [hSj j (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hdeg j; omega),
      neg_zero]
  have hSm : ∑ k ∈ Finset.range p, (k : ZMod p) ^ m * ((k.choose m : ℕ) : ZMod p) ≠ 0 := by
    rw [hSj m le_rfl, hhdef, Polynomial.coeff_C_mul]
    have hmon := (monic_descPochhammer (ZMod p) m).coeff_natDegree
    rw [descPochhammer_natDegree] at hmon
    rw [hmon, mul_one]
    exact neg_ne_zero.mpr (inv_ne_zero (hfac m (by omega)))
  have hdiv : ∀ n, (Polynomial.X - 1) ^ n ∣ q ↔ Polynomial.X ^ n ∣ Polynomial.taylor 1 q := by
    intro n
    have hback : ∀ f : Polynomial (ZMod p), Polynomial.taylor (-1) (Polynomial.taylor 1 f) = f := by
      intro f
      rw [Polynomial.taylor_taylor]
      norm_num
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨Polynomial.taylor 1 s, ?_⟩
      rw [hs]
      simp [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.pow_comp]
    · rintro ⟨s, hs⟩
      refine ⟨Polynomial.taylor (-1) s, ?_⟩
      rw [← hback q, hs, Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
      have hX : (Polynomial.X + Polynomial.C (-1) : Polynomial (ZMod p)) = Polynomial.X - 1 := by
        simp [sub_eq_add_neg]
      rw [hX]
  constructor
  · rw [Set.mem_setOf_eq, hnpoly]
    exact (hdiv m).mpr (Polynomial.X_pow_dvd_iff.mpr (fun j hj => by
      rw [hcoef j]; exact hSlt j hj))
  · intro n hn
    rw [Set.mem_setOf_eq, hnpoly] at hn
    by_contra hlt
    push_neg at hlt
    have h1 := Polynomial.X_pow_dvd_iff.mp ((hdiv n).mp hn) m hlt
    rw [hcoef m] at h1
    exact hSm h1
