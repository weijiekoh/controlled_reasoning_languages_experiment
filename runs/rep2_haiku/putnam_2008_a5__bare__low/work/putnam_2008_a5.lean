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
  obtain ⟨O, z, hz, hobs⟩ := hfg
  by_contra hcon
  push Not at hcon
  obtain ⟨hf_deg, hg_deg⟩ := hcon
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  rw [show m + 1 - 1 = m by omega] at hf_deg hg_deg
  -- finite difference identity for real polynomials of low degree
  have hsum : ∀ P : Polynomial ℝ, P.natDegree < m →
      ∑ k ∈ Finset.range (m + 1), ((-1:ℝ) ^ (m - k) * (m.choose k : ℝ)) * P.eval ((1 + k : ℕ) : ℝ) = 0 := by
    intro P hP
    have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) (n := m) hP) 1
    rw [fwdDiff_iter_eq_sum_shift] at h
    simp only [Pi.zero_apply, zsmul_eq_mul, nsmul_eq_mul, mul_one] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring_nf
  set ω : ℂ := Complex.exp (Complex.I * 2 * Real.pi / ((m + 1 : ℕ) : ℂ)) with hω
  have hexp : ∀ k : ℕ, Complex.exp (Complex.I * 2 * Real.pi * k / ((m + 1 : ℕ) : ℂ)) = ω ^ k := by
    intro k
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hprim : ω ≠ 1 := by
    have h1 : ω = Complex.exp (2 * Real.pi * Complex.I / ((m + 1 : ℕ) : ℂ)) := by
      rw [hω]; congr 1; ring
    rw [h1]
    exact (Complex.isPrimitiveRoot_exp (m + 1) (by omega)).ne_one (by omega)
  have hpt : ∀ j ∈ Finset.range (m + 1),
      ((f.eval ((1 + j : ℕ) : ℝ) : ℝ) : ℂ) + Complex.I * ((g.eval ((1 + j : ℕ) : ℝ) : ℝ) : ℂ)
        = O + z * ω ^ (1 + j) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have := hobs (1 + j) (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hexp] at this
    exact this
  have hf := hsum f hf_deg
  have hg := hsum g hg_deg
  have hkey : ∑ k ∈ Finset.range (m + 1), (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) * (O + z * ω ^ (1 + k)) = 0 := by
    calc ∑ k ∈ Finset.range (m + 1), (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) * (O + z * ω ^ (1 + k))
        = ∑ k ∈ Finset.range (m + 1), (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) *
            (((f.eval ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) + Complex.I * ((g.eval ((1 + k : ℕ) : ℝ) : ℝ) : ℂ)) :=
          Finset.sum_congr rfl (fun j hj => by rw [hpt j hj])
      _ = (((∑ k ∈ Finset.range (m + 1), (-1:ℝ) ^ (m - k) * (m.choose k : ℝ) * f.eval ((1 + k : ℕ) : ℝ) : ℝ)) : ℂ)
            + Complex.I * ((∑ k ∈ Finset.range (m + 1), (-1:ℝ) ^ (m - k) * (m.choose k : ℝ) * g.eval ((1 + k : ℕ) : ℝ) : ℝ) : ℂ) := by
          simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [hf, hg]; simp
  have hc : ∀ k : ℕ, (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) * (O + z * ω ^ (1 + k))
      = O * (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) + (z * ω) * ((((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) * ω ^ k) := by
    intro k; ring
  have A : ∑ k ∈ Finset.range (m + 1), (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) = 0 := by
    have h := add_pow (1:ℂ) (-1) m
    rw [show (1:ℂ) + -1 = 0 by ring, zero_pow (by omega)] at h
    simp only [one_pow, one_mul] at h
    rw [h]
    push_cast
    rfl
  have B : ∑ k ∈ Finset.range (m + 1), (((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) : ℝ) : ℂ) * ω ^ k = (ω - 1) ^ m := by
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, A, B] at hkey
  have hne : (ω - 1) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hprim)
  have : z * ω * (ω - 1) ^ m = 0 := by simpa using hkey
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hz' : (z : ℂ) ≠ 0 := hz
  exact mul_ne_zero (mul_ne_zero hz' hω0) hne this
