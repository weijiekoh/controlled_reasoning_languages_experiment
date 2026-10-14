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
: (f.natDegree ≥ n - 1 ∨ g.natDegree ≥ n - 1) :=
by
  by_contra hcon
  push Not at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨O, z, hz, h⟩ := hfg
  -- forward difference kills polynomials of degree < m
  have key : ∀ (m : ℕ) (q : Polynomial ℝ), q.natDegree < m → ∀ x : ℝ,
      ∑ k ∈ Finset.range (m + 1), ((-1 : ℝ) ^ (m - k) * (m.choose k : ℝ)) * q.eval (x + k) = 0 := by
    intro m q hq x
    have hF : (fun y : ℝ => q.eval y) = ∑ i ∈ Finset.range m, (q.coeff i) • (fun r : ℝ => r ^ i) := by
      funext y
      simp [Finset.sum_apply, Polynomial.eval_eq_sum_range' hq]
    have h0 : (fwdDiff (1 : ℝ))^[m] (fun y : ℝ => q.eval y) = 0 := by
      rw [hF, fwdDiff_iter_finsetSum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [fwdDiff_iter_const_smul, fwdDiff_iter_pow_eq_zero_of_lt (Finset.mem_range.mp hi), smul_zero]
    have h2 : (fwdDiff (1 : ℝ))^[m] (fun y : ℝ => q.eval y) x = 0 := by
      rw [h0]; rfl
    rw [fwdDiff_iter_eq_sum_shift] at h2
    simp only [zsmul_eq_mul, nsmul_eq_mul] at h2
    push_cast at h2
    simpa [add_comm] using h2
  set m := n - 1 with hm_def
  have hm1 : 1 ≤ m := by omega
  have hmn : m + 1 = n := by omega
  set ω : ℂ := Complex.exp (Complex.I * 2 * Real.pi / n) with hω
  have hωpow : ∀ k : ℕ, Complex.exp (Complex.I * 2 * Real.pi * k / n) = ω ^ k := by
    intro k
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hωprim : IsPrimitiveRoot ω n := by
    have h0 := Complex.isPrimitiveRoot_exp n (by omega)
    have e : ω = Complex.exp (2 * Real.pi * Complex.I / n) := by
      rw [hω]; congr 1; ring
    rw [e]; exact h0
  have hωne1 : ω ≠ 1 := hωprim.ne_one (by omega)
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hωm1 : ω + -1 ≠ 0 := by
    intro h'; apply hωne1; linear_combination h'
  have hpt : ∀ k : ℕ, k ≤ m →
      ((f.eval (1 + (k : ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k : ℝ)) : ℝ) : ℂ) = O + z * ω ^ (k + 1) := by
    intro k hk
    have := h (k + 1) (by rw [Set.mem_Icc]; constructor <;> omega)
    have e : ((k + 1 : ℕ) : ℝ) = 1 + (k : ℝ) := by push_cast; ring
    rw [hωpow (k + 1), e] at this
    exact this
  have hkf := key m f (by omega) 1
  have hkg := key m g (by omega) 1
  have hf' : ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * ((f.eval (1 + (k : ℝ)) : ℝ) : ℂ) = 0 := by
    exact_mod_cast hkf
  have hg' : ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * ((g.eval (1 + (k : ℝ)) : ℝ) : ℂ) = 0 := by
    exact_mod_cast hkg
  have hsum : ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * (O + z * ω ^ (k + 1)) = 0 := by
    calc ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * (O + z * ω ^ (k + 1))
        = ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) *
            (((f.eval (1 + (k : ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k : ℝ)) : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hpt k (by have := Finset.mem_range.mp hk; omega)]
      _ = ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * ((f.eval (1 + (k : ℝ)) : ℝ) : ℂ)
          + Complex.I * ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * ((g.eval (1 + (k : ℝ)) : ℝ) : ℂ) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ = 0 := by rw [hf', hg']; ring
  have hS : ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) = 0 := by
    have := add_pow (1 : ℂ) (-1) m
    simp only [one_pow, one_mul] at this
    rw [show (1 : ℂ) + -1 = 0 by ring, zero_pow (by omega)] at this
    exact this.symm
  have hT : ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * ω ^ (k + 1)
      = ω * (ω + -1) ^ m := by
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have expand : ∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * (O + z * ω ^ (k + 1))
      = O * (∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)))
        + z * (∑ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) * ω ^ (k + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, hS, hT] at expand
  have hne : z * ω * (ω + -1) ^ m ≠ 0 :=
    mul_ne_zero (mul_ne_zero hz hω0) (pow_ne_zero m hωm1)
  apply hne
  linear_combination -expand
