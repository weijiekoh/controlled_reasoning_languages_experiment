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
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨O, z, hz, hyp⟩ := hfg
  by_contra hcon
  push_neg at hcon
  obtain ⟨hf, hg⟩ := hcon
  have hf' : f.natDegree < m := by simpa using hf
  have hg' : g.natDegree < m := by simpa using hg
  have hprim := Complex.isPrimitiveRoot_exp (m + 1) (by omega)
  have hω1 := hprim.ne_one (by omega)
  have hω0 : Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hpow : ∀ k : ℕ, Complex.exp (Complex.I * 2 * Real.pi * k / ((m + 1 : ℕ) : ℂ))
      = (Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ))) ^ k := by
    intro k
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  generalize Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ)) = ω at hω1 hω0 hpow hprim
  -- key identity: m-th finite difference kills polynomials of degree < m
  have key : ∀ Q : Polynomial ℂ, Q.natDegree < m →
      ∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ)) • Q.eval (1 + (k : ℂ)) = 0 := by
    intro Q hQ
    have hE : (fun r : ℂ => Q.eval r) = fun r => ∑ k ∈ Finset.range m, Q.coeff k * r ^ k := by
      funext r
      conv_lhs => rw [Polynomial.as_sum_range' Q m hQ]
      simp [Polynomial.eval_finset_sum]
    have h1 := fwdDiff_iter_eq_sum_shift (1 : ℂ) (fun r : ℂ => Q.eval r) m 1
    have h2 : (fwdDiff (1 : ℂ))^[m] (fun r : ℂ => Q.eval r) = 0 := by
      rw [hE]; exact fwdDiff_iter_sum_mul_pow_eq_zero _
    have h4 : ((fwdDiff (1 : ℂ))^[m] (fun r : ℂ => Q.eval r)) 1 = 0 := by
      rw [h2]; rfl
    rw [h1] at h4
    simp only [nsmul_eq_mul, mul_one] at h4
    exact h4
  have hcoef : ∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℂ) = 0 := by
    have h := add_pow (1 : ℂ) (-1) m
    rw [add_neg_cancel] at h
    simp only [one_pow, one_mul] at h
    push_cast
    rw [zero_pow (by omega)] at h
    exact h.symm
  have hcoef1 : ∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℂ) * ω ^ k = (ω - 1) ^ m := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℂ,
      Q = f.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * g.map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hQdeg : Q.natDegree < m := by
    rw [hQdef]
    have h1 := Polynomial.natDegree_add_le (f.map (algebraMap ℝ ℂ))
      (Polynomial.C Complex.I * g.map (algebraMap ℝ ℂ))
    have h2 := Polynomial.natDegree_C_mul_le Complex.I (g.map (algebraMap ℝ ℂ))
    have h3 : (f.map (algebraMap ℝ ℂ)).natDegree ≤ f.natDegree := Polynomial.natDegree_map_le
    have h4 : (g.map (algebraMap ℝ ℂ)).natDegree ≤ g.natDegree := Polynomial.natDegree_map_le
    omega
  have hev : ∀ (p : Polynomial ℝ) (x : ℝ), p.eval₂ (algebraMap ℝ ℂ) (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
    intro p x
    have := Polynomial.eval₂_hom (p := p) (algebraMap ℝ ℂ) x
    simpa using this
  have hQeval : ∀ x : ℝ, Q.eval (x : ℂ) = ((f.eval x : ℝ) : ℂ) + Complex.I * ((g.eval x : ℝ) : ℂ) := by
    intro x
    rw [hQdef]
    simp only [Polynomial.eval_map, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hev]
  have hQval : ∀ k ∈ Finset.range (m + 1), Q.eval (1 + (k : ℂ)) = O + z * ω ^ (k + 1) := by
    intro k hk
    have hk' := hyp (k + 1) (by
      rw [Finset.mem_range] at hk
      rw [Set.mem_Icc]
      constructor <;> omega)
    have hpt : (1 + (k : ℂ)) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hpt, hQeval, hk', hpow]
  have hsum := key Q hQdeg
  have hsum2 : ∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℂ) * (O + z * ω ^ (k + 1))
      = ∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ)) • Q.eval (1 + (k : ℂ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hQval k hk, zsmul_eq_mul]
  rw [hsum] at hsum2
  have hexp : ∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℂ) * (O + z * ω ^ (k + 1))
      = O * (∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℂ))
        + z * ω * (∑ k ∈ Finset.range (m + 1), (((-1 : ℤ) ^ (m - k) * (m.choose k : ℤ) : ℤ) : ℂ) * ω ^ k) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [hexp, hcoef, hcoef1, mul_zero, zero_add] at hsum2
  exact mul_ne_zero (mul_ne_zero hz hω0) (pow_ne_zero _ (sub_ne_zero.mpr hω1)) hsum2
