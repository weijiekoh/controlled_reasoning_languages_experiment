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
  haveI := Fact.mk pprime
  have hp2 : 2 ≤ p := pprime.two_le
  have hm1 : (p - 1) / 2 ≥ 1 := by obtain ⟨r, hr⟩ := podd; omega
  have hpm : p - 1 = 2 * ((p - 1) / 2) := by obtain ⟨r, hr⟩ := podd; omega
  -- the operator X * d/dX
  have step : ∀ (k : ℕ) (g : Polynomial (ZMod p)), (X - 1) ^ k ∣ g →
      (X - 1) ^ (k - 1) ∣ X * derivative g := by
    intro k g hg
    rcases k with _ | k
    · simp
    · obtain ⟨h, rfl⟩ := hg
      refine ⟨X * (C ((k : ZMod p) + 1) * h + (X - 1) * derivative h), ?_⟩
      rw [derivative_mul, derivative_pow_succ]
      simp only [derivative_sub, derivative_X, derivative_one, Nat.add_sub_cancel]
      ring
  have iter : ∀ (j k : ℕ) (g : Polynomial (ZMod p)), (X - 1) ^ k ∣ g →
      (X - 1) ^ (k - j) ∣ (fun g => X * derivative g)^[j] g := by
    intro j
    induction j with
    | zero => intro k g h; simpa using h
    | succ j ih =>
      intro k g h
      rw [Function.iterate_succ_apply]
      have := ih (k - 1) _ (step k g h)
      rwa [show k - 1 - j = k - (j + 1) by omega] at this
  have c1 : ∀ (n : ℕ) (g : Polynomial (ZMod p)), (X * derivative g).coeff n = (n : ZMod p) * g.coeff n := by
    intro n g
    rcases n with _ | n
    · simp
    · rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring
  have coeffD : ∀ (j n : ℕ) (g : Polynomial (ZMod p)),
      ((fun g => X * derivative g)^[j] g).coeff n = (n : ZMod p) ^ j * g.coeff n := by
    intro j
    induction j with
    | zero => intro n g; simp
    | succ j ih =>
      intro n g
      rw [Function.iterate_succ_apply, ih, c1, pow_succ]
      ring
  have evalsum : ∀ g : Polynomial (ZMod p), (∀ N, p ≤ N → g.coeff N = 0) →
      eval 1 g = ∑ i ∈ Finset.range p, g.coeff i := by
    intro g hg
    have : g.natDegree < p := by
      have := natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => hg N (by omega) : ∀ N, p - 1 < N → g.coeff N = 0)
      omega
    rw [eval_eq_sum_range' this]
    simp
  -- S = sum X^i = (X-1)^(p-1)
  have hX1 : (X - 1 : Polynomial (ZMod p)) ≠ 0 := by
    simpa using X_sub_C_ne_zero (1 : ZMod p)
  have hS : (X - 1 : Polynomial (ZMod p)) ^ (p - 1) = ∑ i ∈ Finset.range p, (X : Polynomial (ZMod p)) ^ i := by
    apply mul_left_cancel₀ hX1
    have h1 : (∑ i ∈ Finset.range p, (X : Polynomial (ZMod p)) ^ i) * (X - 1) = X ^ p - 1 :=
      geom_sum_mul _ _
    have h2 : (X - 1 : Polynomial (ZMod p)) ^ p = X ^ p - 1 := by
      rw [sub_pow_char, one_pow]
    have h3 : (X - 1 : Polynomial (ZMod p)) * (X - 1) ^ (p - 1) = (X - 1) ^ p := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3, h2, ← h1]
    ring
  have hcoeffS : ∀ k, (∑ i ∈ Finset.range p, (X : Polynomial (ZMod p)) ^ i).coeff k
      = if k < p then 1 else 0 := by
    intro k
    simp [coeff_X_pow]
  -- q = D^m (X-1)^(p-1)
  have hqS : q = (fun g => X * derivative g)^[(p - 1) / 2] ((X - 1) ^ (p - 1)) := by
    ext k
    rw [coeffD, hS, hcoeffS, hq]
    by_cases hk : k < p
    · simp only [hk, if_true, mul_one]
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [ha0.1]
        simp [zero_pow (show (p - 1) / 2 ≠ 0 by omega)]
      · rw [haother ⟨k, Set.mem_Icc.mpr ⟨by omega, by omega⟩⟩]
        rw [ZMod.natCast_mod, Nat.cast_pow]
    · rw [if_neg hk, mul_zero]
      exact ha0.2 k (by omega)
  constructor
  · show npoly ((p - 1) / 2) ∣ q
    rw [hnpoly, hqS]
    have := iter ((p - 1) / 2) (p - 1) ((X - 1) ^ (p - 1)) dvd_rfl
    rwa [show p - 1 - (p - 1) / 2 = (p - 1) / 2 by omega] at this
  · intro n hn
    rw [Set.mem_setOf_eq, hnpoly] at hn
    by_contra hlt
    push_neg at hlt
    have h1 : (X - 1 : Polynomial (ZMod p)) ^ ((p - 1) / 2 + 1) ∣ q :=
      (pow_dvd_pow _ (Nat.succ_le_of_lt hlt)).trans hn
    have h2 := iter ((p - 1) / 2) ((p - 1) / 2 + 1) q h1
    have h3 : (X - 1 : Polynomial (ZMod p)) ∣ (fun g => X * derivative g)^[(p - 1) / 2] q := by
      simpa [show (p - 1) / 2 + 1 - (p - 1) / 2 = 1 by omega] using h2
    have h4 : eval 1 ((fun g => X * derivative g)^[(p - 1) / 2] q) = 0 := by
      obtain ⟨r, hr⟩ := h3
      rw [hr]
      simp
    rw [evalsum] at h4
    · have hsum : ∑ i ∈ Finset.range p, ((fun g => X * derivative g)^[(p - 1) / 2] q).coeff i
          = ∑ i ∈ Finset.range p, (i : ZMod p) ^ (p - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [coeffD, hq]
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [ha0.1]
          simp [zero_pow (show (p - 1) / 2 ≠ 0 by omega), zero_pow (show p - 1 ≠ 0 by omega)]
        · rw [haother ⟨i, Set.mem_Icc.mpr ⟨by omega, by omega⟩⟩]
          simp only [Nat.cast_pow, ZMod.natCast_mod]
          rw [← pow_add]
          congr 1
          omega
      have hsum' : ∑ i ∈ Finset.range p, (i : ZMod p) ^ (p - 1) = -1 := by
        obtain ⟨n, hn'⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
        subst hn'
        have hn0 : n ≠ 0 := by omega
        rw [Finset.sum_range_succ']
        have hz : ∀ i ∈ Finset.range n, ((i + 1 : ℕ) : ZMod (n + 1)) ^ (n + 1 - 1) = 1 := by
          intro i hi
          rw [Finset.mem_range] at hi
          apply ZMod.pow_card_sub_one_eq_one
          intro h0
          rw [ZMod.natCast_eq_zero_iff (i + 1) (n + 1)] at h0
          have := Nat.le_of_dvd (by omega) h0
          omega
        rw [Finset.sum_congr rfl hz]
        simp only [Nat.add_sub_cancel, Nat.cast_zero, zero_pow hn0, add_zero,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have h0 : (n : ZMod (n + 1)) + 1 = 0 := by
          have := ZMod.natCast_self (n + 1)
          push_cast at this
          exact this
        exact eq_neg_of_add_eq_zero_left h0
      rw [hsum, hsum'] at h4
      exact (neg_ne_zero.mpr one_ne_zero) h4
    · intro N hN
      rw [coeffD, hq, ha0.2 N (by omega), mul_zero]
