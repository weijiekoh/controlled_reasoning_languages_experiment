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
  push_neg at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨O, z, hz, hO⟩ := hfg
  obtain ⟨N, hNdef⟩ : ∃ N, N = n - 1 := ⟨_, rfl⟩
  have hnN : n = N + 1 := by omega
  have hN2 : 2 ≤ N := by omega
  have hA : ∀ p : Polynomial ℝ, p.natDegree < N →
      ∑ j ∈ Finset.range (N+1), ((-1:ℤ)^(N-j) * (N.choose j : ℤ)) • p.eval (1 + (j:ℝ)) = 0 := by
    intro p hp
    have h1 : (fwdDiff (1:ℝ))^[N] (fun r => p.eval r) = 0 := by
      have e : (fun r : ℝ => p.eval r) = fun r => ∑ i ∈ Finset.range N, p.coeff i * r^i :=
        funext fun r => Polynomial.eval_eq_sum_range' hp r
      rw [e]
      exact fwdDiff_iter_sum_mul_pow_eq_zero (fun i => p.coeff i)
    have h2 := congrFun h1 1
    rw [fwdDiff_iter_eq_sum_shift] at h2
    simpa using h2
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℂ, ω = Complex.exp (Complex.I * 2 * Real.pi / n) := ⟨_, rfl⟩
  have hexp : ∀ k : ℕ, Complex.exp (Complex.I * 2 * Real.pi * k / n) = ω ^ k := by
    intro k
    rw [hωdef, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hB : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * ω^j = (ω-1)^N := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hω1 : ω - 1 ≠ 0 := by
    intro h
    have h1 : ω = 1 := by linear_combination h
    rw [hωdef, Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hmn : (m : ℂ) * n = 1 := by
      field_simp at hm
      linear_combination -hm
    have hmn' : m * (n : ℤ) = 1 := by exact_mod_cast hmn
    have h3 : (n : ℤ) ≥ 3 := by omega
    rcases (show m ≤ 0 ∨ m ≥ 1 by omega) with h4 | h4 <;> nlinarith
  have hpt : ∀ j ∈ Finset.range (N+1), (1 + j : ℕ) ∈ Icc 1 n := by
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [mem_Icc]
    omega
  have hk : ∀ j ∈ Finset.range (N+1),
      ((f.eval (1 + (j:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (j:ℝ)) : ℝ) : ℂ) = O + z * ω^(1+j) := by
    intro j hj
    have h := hO (1+j) (hpt j hj)
    rw [hexp] at h
    have e : ((1+j : ℕ) : ℝ) = 1 + (j:ℝ) := by push_cast; ring
    rw [e] at h
    exact h
  have hAC : ∀ p : Polynomial ℝ, p.natDegree < N →
      ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * ((p.eval (1 + (j:ℝ)) : ℝ) : ℂ) = 0 := by
    intro p hp
    have h := congrArg (fun x : ℝ => (x : ℂ)) (hA p hp)
    simp only [zsmul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_zero] at h
    exact h
  have hf' : f.natDegree < N := by omega
  have hg' : g.natDegree < N := by omega
  have h1' : (1 : Polynomial ℝ).natDegree < N := by simp; omega
  have Sw : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) = 0 := by
    have := hAC 1 h1'
    simpa using this
  have key : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) *
      (((f.eval (1 + (j:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (j:ℝ)) : ℝ) : ℂ))
      = ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * (O + z * ω^(1+j)) :=
    Finset.sum_congr rfl (fun j hj => by rw [hk j hj])
  have eF : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) *
      (((f.eval (1 + (j:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (j:ℝ)) : ℝ) : ℂ))
      = ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * ((f.eval (1 + (j:ℝ)) : ℝ) : ℂ)
        + Complex.I * ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * ((g.eval (1 + (j:ℝ)) : ℝ) : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have eR : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * (O + z * ω^(1+j))
      = O * ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ)
        + ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * (z * ω^(1+j)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hT : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * (z * ω^(1+j))
      = z * (ω * (ω-1)^N) := by
    have e2 : ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * (z * ω^(1+j))
        = z * (ω * ∑ j ∈ Finset.range (N+1), (((-1:ℤ)^(N-j) * (N.choose j : ℤ) : ℤ) : ℂ) * ω^j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e2, hB]
  have Sf := hAC f hf'
  have Sg := hAC g hg'
  have hfin : z * (ω * (ω-1)^N) = 0 := by
    linear_combination (-1 : ℂ) * hT - eR - key + eF + Sf + Complex.I * Sg - O * Sw
  have hω0 : ω ≠ 0 := by
    rw [hωdef]; exact Complex.exp_ne_zero _
  rcases mul_eq_zero.mp hfin with h | h
  · exact hz h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hω0 h'
    · exact pow_ne_zero N hω1 h'
