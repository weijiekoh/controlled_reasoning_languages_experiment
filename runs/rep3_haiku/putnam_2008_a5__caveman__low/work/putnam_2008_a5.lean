import Mathlib

open Filter Topology Set

/--
Let $n \geq 3$ be an integer. Let $f(x)$ and $g(x)$ be polynomials with real coefficients such that the points $(f(1), g(1)), (f(2), g(2)), \dots, (f(n), g(n))$ in $\mathbb{R}^2$ are the vertices of a regular $n$-gon in counterclockwise order. Prove that at least one of $f(x)$ and $g(x)$ has degree greater than or equal to $n-1$.
-/
theorem putnam_2008_a5
(n : ℕ)
(nge3 : n ≥ 3)
(f g : Polynomial ℝ)
(hfg : ∃ O z : ℂ, z ≠ 0 ∧ ∀ k : ℕ, k ∈ Icc 1 n → (f.eval (k : ℝ)) + Complex.I * (g.eval (k : ℝ)) = O + z * Complex.exp (Complex.I * 2 * Real.pi * k / n))
: (f.natDegree ≥ n - 1 ∨ g.natDegree ≥ n - 1) := by
  obtain ⟨O, z, hz, h⟩ := hfg
  by_contra hcon
  push_neg at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨m, hm⟩ : ∃ m, m = n - 1 := ⟨_, rfl⟩
  rw [← hm] at hf hg
  have hm2 : 2 ≤ m := by omega
  have key : ∀ p : Polynomial ℝ, p.natDegree < m →
      ∑ k ∈ Finset.range (m+1), ((-1:ℝ)^(m-k) * (m.choose k : ℝ)) * p.eval (1 + (k:ℝ)) = 0 := by
    intro p hp
    have hpow : ∀ j, j < m → ∑ k ∈ Finset.range (m+1), ((-1:ℝ)^(m-k) * (m.choose k : ℝ)) * (1 + (k:ℝ))^j = 0 := by
      intro j hj
      have := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hj) 1
      rw [fwdDiff_iter_eq_sum_shift] at this
      simp only [Pi.zero_apply, zsmul_eq_mul, nsmul_eq_mul, mul_one] at this
      push_cast at this
      exact this
    simp only [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    have e : ∑ k ∈ Finset.range (m+1), ((-1:ℝ)^(m-k) * (m.choose k : ℝ)) * (p.coeff j * (1 + (k:ℝ))^j)
        = p.coeff j * ∑ k ∈ Finset.range (m+1), ((-1:ℝ)^(m-k) * (m.choose k : ℝ)) * (1 + (k:ℝ))^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros; ring
    rw [e, hpow j (Finset.mem_range.mp hj), mul_zero]
  have keyC : ∀ p : Polynomial ℝ, p.natDegree < m →
      ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * ((p.eval (1 + (k:ℝ)) : ℝ) : ℂ) = 0 := by
    intro p hp
    have h2 := congrArg (fun x : ℝ => (x : ℂ)) (key p hp)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero, Complex.ofReal_pow,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_natCast] at h2
    exact h2
  have hw1C : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) = 0 := by
    have := keyC 1 (by simp; omega)
    simpa using this
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℂ, ω = Complex.exp (Complex.I * 2 * Real.pi / n) := ⟨_, rfl⟩
  have hH : ∀ k ∈ Finset.range (m+1),
      ((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ) = O + z * ω^(k+1) := by
    intro k hk
    have hk' : k + 1 ∈ Icc 1 n := by
      rw [Finset.mem_range] at hk
      simp only [Set.mem_Icc]; omega
    have := h (k+1) hk'
    have e : Complex.exp (Complex.I * 2 * Real.pi * ((k+1 : ℕ) : ℂ) / n) = ω^(k+1) := by
      rw [hωdef, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e] at this
    have hc : (1 + (k:ℝ)) = ((k+1 : ℕ) : ℝ) := by push_cast; ring
    rw [hc]
    exact this
  have hωne : ω - 1 ≠ 0 := by
    intro h0
    have h1 : ω = 1 := by linear_combination h0
    rw [hωdef, Complex.exp_eq_one_iff] at h1
    obtain ⟨t, ht⟩ := h1
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hpi : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hmul : (t:ℂ) * (n:ℂ) = 1 := by
      have e1 : Complex.I * 2 * Real.pi / n * n = Complex.I * 2 * Real.pi := div_mul_cancel₀ _ hn0
      rw [ht] at e1
      have e2 : ((t:ℂ) * n - 1) * (2 * (Real.pi:ℂ) * Complex.I) = 0 := by linear_combination e1
      rcases mul_eq_zero.mp e2 with h3 | h3
      · linear_combination h3
      · exact absurd h3 hpi
    have hZ : t * (n:ℤ) = 1 := by exact_mod_cast hmul
    have hd : (n:ℤ) ∣ 1 := ⟨t, by linarith⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  have hC : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (O + z * ω^(k+1)) = 0 := by
    have hA := keyC f hf
    have hB := keyC g hg
    have hsum : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (O + z * ω^(k+1))
        = ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hH k hk]
    rw [hsum]
    have e : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ))
        = ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * ((f.eval (1 + (k:ℝ)) : ℝ) : ℂ)
          + Complex.I * ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros; ring
    rw [e, hA, hB]; ring
  have hfin : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (O + z * ω^(k+1))
      = O * ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ))
        + z * ω * ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * ω^k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpowsum : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * ω^k = (ω - 1)^m := by
    rw [show ω - 1 = ω + (-1) by ring, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfin, hpowsum, hw1C] at hC
  have hpos : z * ω * (ω - 1)^m ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero hz ?_) (pow_ne_zero _ hωne)
    intro h0
    rw [hωdef] at h0
    exact Complex.exp_ne_zero _ h0
  apply hpos
  linear_combination hC
