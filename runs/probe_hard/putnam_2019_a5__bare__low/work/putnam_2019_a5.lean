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
  haveI : Fact p.Prime := ⟨pprime⟩
  have hp3 : 3 ≤ p := by
    rcases pprime.eq_two_or_odd' with h | h
    · subst h; exact absurd podd (by decide)
    · have := pprime.two_le; rcases podd with ⟨t, ht⟩; omega
  obtain ⟨m, hm⟩ : ∃ m, m = (p - 1) / 2 := ⟨_, rfl⟩
  have hp2 : p - 1 = 2 * m := by rcases podd with ⟨t, ht⟩; omega
  have hm1 : 1 ≤ m := by omega
  set f : Polynomial (ZMod p) := (Polynomial.X - 1) ^ (p - 1) with hf
  have hX1 : (Polynomial.X - 1 : Polynomial (ZMod p)) ≠ 0 := by simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
  have hfs : f = ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p)) ^ i := by
    apply mul_right_cancel₀ hX1
    rw [geom_sum_mul, hf, ← pow_succ, Nat.sub_add_cancel pprime.one_le]
    have : ((Polynomial.X : Polynomial (ZMod p)) - 1) ^ p = Polynomial.X ^ p - 1 ^ p := sub_pow_char _ _
    rw [this]; simp
  have hfc : ∀ k, f.coeff k = if k < p then 1 else 0 := by
    intro k
    rw [hfs, Polynomial.finset_sum_coeff]
    simp [Polynomial.coeff_X_pow, Finset.sum_ite_eq']
  let D : Polynomial (ZMod p) → Polynomial (ZMod p) := fun P => Polynomial.X * Polynomial.derivative P
  have hD : ∀ j P k, (D^[j] P).coeff k = (k : ZMod p) ^ j * P.coeff k := by
    intro j
    induction j with
    | zero => intro P k; simp
    | succ j ih =>
      intro P k
      rw [Function.iterate_succ_apply, ih]
      cases k with
      | zero => simp [D]
      | succ n =>
        simp only [D, Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
        push_cast; ring
  have hq : q = D^[m] f := by
    ext k
    rw [hq k, hD, hfc]
    by_cases h0 : k = 0
    · subst h0; simp [ha0.1]; intro _; exact (zero_pow (by omega)).symm
    by_cases hk : k < p
    · have := haother ⟨k, by omega, by omega⟩
      rw [this, ZMod.natCast_mod]; simp [hk, ← hm]
    · rw [ha0.2 k (by omega)]; simp [hk]
  have key : ∀ j, j ≤ p - 1 → ∃ g : Polynomial (ZMod p), D^[j] f = (Polynomial.X - 1) ^ (p - 1 - j) * g ∧
      g.eval 1 = ∏ i ∈ Finset.range j, ((p - 1 - i : ℕ) : ZMod p) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨1, by simp [hf], by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨g, hg, hg1⟩ := ih (by omega)
      have hN : p - 1 - j = (p - 1 - (j+1)) + 1 := by omega
      refine ⟨Polynomial.X * (((p - 1 - j : ℕ) : ZMod p) • g + (Polynomial.X - 1) * Polynomial.derivative g), ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hg]
        simp only [D]
        rw [hN]
        simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_one]
        rw [← hN]
        rw [hN] 
        simp only [Polynomial.smul_eq_C_mul]
        push_cast [Nat.cast_add]
        simp
        ring
      · rw [Finset.prod_range_succ, ← hg1]
        simp [Polynomial.eval_smul]
        ring
  obtain ⟨g, hg, hg1⟩ := key m (by omega)
  have hpm : p - 1 - m = m := by omega
  rw [hpm] at hg
  have hg0 : g.eval 1 ≠ 0 := by
    rw [hg1]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  constructor
  · show npoly _ ∣ q
    rw [hnpoly, hq, hg]
    simp only [putnam_2019_a5_solution]; rw [← hm]
    exact dvd_mul_right _ _
  · intro n hn
    simp only [putnam_2019_a5_solution]; rw [← hm]
    by_contra hlt
    push_neg at hlt
    have h1 : (Polynomial.X - 1 : Polynomial (ZMod p)) ^ (m+1) ∣ q := by
      have : npoly n ∣ q := hn
      rw [hnpoly] at this
      exact (pow_dvd_pow _ hlt).trans this
    rw [hq, hg, pow_succ] at h1
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero m hX1)).mp h1
    have h3 := Polynomial.dvd_iff_isRoot.mp h2
    exact hg0 h3
