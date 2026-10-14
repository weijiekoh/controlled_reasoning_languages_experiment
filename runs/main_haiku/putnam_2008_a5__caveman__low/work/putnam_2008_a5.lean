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
  by_contra hcon
  push Not at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨O, z, hz, hval⟩ := hfg
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m + 1 - 1 = m := by omega
  rw [hm] at hf hg
  have key : ∀ p : Polynomial ℝ, p.natDegree < m →
      ∑ k ∈ Finset.range (m+1), ((-1:ℤ)^(m-k) * (m.choose k : ℤ)) • p.eval (1 + (k:ℝ)) = 0 := by
    intro p hp
    have h0 : (fwdDiff (1:ℝ))^[m] (fun r => p.eval r) = 0 := by
      have e : (fun r => p.eval r) = fun r => ∑ k ∈ Finset.range m, p.coeff k * r ^ k :=
        funext (fun r => Polynomial.eval_eq_sum_range' hp r)
      rw [e]; exact fwdDiff_iter_sum_mul_pow_eq_zero _
    have h1 := congrFun h0 1
    rw [fwdDiff_iter_eq_sum_shift] at h1
    simpa [nsmul_eq_mul] using h1
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ)) with hω
  have hω1 : ω ≠ 1 := by
    have hp := Complex.isPrimitiveRoot_exp (m + 1) (by omega)
    exact hp.ne_one (by omega)
  have hpt : ∀ k ∈ Finset.range (m+1),
      (((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ)) = O + z * ω ^ (k+1) := by
    intro k hk
    have hk' : k + 1 ∈ Icc 1 (m + 1) := by
      simp only [Finset.mem_range] at hk
      simp only [mem_Icc]; omega
    have h := hval (k+1) hk'
    push_cast at h
    rw [add_comm (1:ℝ) (k:ℝ), h]
    congr 1
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hf0 := key f hf
  have hg0 := key g hg
  have hone := key 1 (by simp; omega)
  have hcomb : ∑ k ∈ Finset.range (m+1), (((-1:ℤ)^(m-k) * (m.choose k : ℤ) : ℤ) : ℂ) *
      (((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ)) = 0 := by
    have ef := congrArg (fun x : ℝ => (x : ℂ)) hf0
    have eg := congrArg (fun x : ℝ => (x : ℂ)) hg0
    simp only [zsmul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_zero] at ef eg
    simp only [mul_add, Finset.sum_add_distrib]
    have : ∑ x ∈ Finset.range (m + 1), ((((-1:ℤ)^(m-x) * (m.choose x : ℤ) : ℤ) : ℂ) * (Complex.I * ((g.eval (1 + (x:ℝ)) : ℝ) : ℂ))) = Complex.I * ∑ x ∈ Finset.range (m + 1), ((((-1:ℤ)^(m-x) * (m.choose x : ℤ) : ℤ) : ℂ) * ((g.eval (1 + (x:ℝ)) : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [this]
    have eg' : ∑ x ∈ Finset.range (m + 1), ((((-1:ℤ)^(m-x) * (m.choose x : ℤ) : ℤ) : ℂ) * ((g.eval (1 + (x:ℝ)) : ℝ) : ℂ)) = 0 := by
      simpa using eg
    rw [eg', ef]; ring
  have hsum : ∑ k ∈ Finset.range (m+1), (((-1:ℤ)^(m-k) * (m.choose k : ℤ) : ℤ) : ℂ) *
      (((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ))
      = O * ∑ k ∈ Finset.range (m+1), (((-1:ℤ)^(m-k) * (m.choose k : ℤ) : ℤ) : ℂ)
        + z * ω * ∑ k ∈ Finset.range (m+1), (((-1:ℤ)^(m-k) * (m.choose k : ℤ) : ℤ) : ℂ) * ω ^ k := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [hpt k hk])]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intros; ring
  have hA : ∑ k ∈ Finset.range (m+1), (((-1:ℤ)^(m-k) * (m.choose k : ℤ) : ℤ) : ℂ) = 0 := by
    have h := add_pow (1:ℂ) (-1) m
    rw [add_neg_cancel, zero_pow (by omega)] at h
    simp only [one_pow, one_mul] at h
    push_cast
    exact h.symm
  have hB : ∑ k ∈ Finset.range (m+1), (((-1:ℤ)^(m-k) * (m.choose k : ℤ) : ℤ) : ℂ) * ω ^ k = (ω - 1) ^ m := by
    have h := add_pow ω (-1) m
    rw [sub_eq_add_neg, h]
    apply Finset.sum_congr rfl; intros; push_cast; ring
  rw [hsum, hA, hB] at hcomb
  have hprod : z * ω * (ω - 1) ^ m = 0 := by linear_combination hcomb
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hz h
    · exact hω0 h
  · exact (pow_ne_zero m (sub_ne_zero.mpr hω1)) h
