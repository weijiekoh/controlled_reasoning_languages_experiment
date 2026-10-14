import Mathlib

open Filter Topology Set

lemma vanish_aux (m : ℕ) (p : Polynomial ℝ) (hp : p.natDegree < m) (y : ℝ) :
    ∑ k ∈ Finset.range (m+1), (-1:ℝ)^(m-k) * (m.choose k : ℝ) * p.eval (y + k) = 0 := by
  have key : ∀ i < m, ∑ k ∈ Finset.range (m+1), (-1:ℝ)^(m-k) * (m.choose k:ℝ) * (y + k)^i = 0 := by
    intro i hi
    have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hi) y
    rw [fwdDiff_iter_eq_sum_shift] at h
    simpa [smul_eq_mul, nsmul_eq_mul] using h
  have ev : ∀ x, p.eval x = ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * x^i :=
    fun x => p.eval_eq_sum_range x
  simp only [ev, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < m := by
    have := Finset.mem_range.mp hi; omega
  calc _ = p.coeff i * ∑ k ∈ Finset.range (m+1), (-1:ℝ)^(m-k) * (m.choose k:ℝ) * (y + k)^i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ = 0 := by rw [key i hi', mul_zero]

theorem putnam_2008_a5
(n : ℕ)
(nge3 : n ≥ 3)
(f g : Polynomial ℝ)
(hfg : ∃ O z : ℂ, z ≠ 0 ∧ ∀ k : ℕ, k ∈ Icc 1 n → (f.eval (k : ℝ)) + Complex.I * (g.eval (k : ℝ)) = O + z * Complex.exp (Complex.I * 2 * Real.pi * k / n))
: (f.natDegree ≥ n - 1 ∨ g.natDegree ≥ n - 1) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨O, z, hz0, hk⟩ := hfg
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have hm : 1 ≤ m := by omega
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = Complex.exp (Complex.I * 2 * Real.pi / ((m+1 : ℕ) : ℂ)) := ⟨_, rfl⟩
  have hpt : ∀ k ∈ Finset.range (m+1),
      ((f.eval (1 + (k:ℝ)) : ℝ) : ℂ) + Complex.I * ((g.eval (1 + (k:ℝ)) : ℝ) : ℂ)
        = O + z * w^(1+k) := by
    intro k hk'
    have hk'' := Finset.mem_range.mp hk'
    have hkI : (1 + k : ℕ) ∈ Icc 1 (m+1) := by simp only [mem_Icc]; omega
    have h := hk (1+k) hkI
    have e : Complex.exp (Complex.I * 2 * Real.pi * ((1+k : ℕ) : ℂ) / ((m+1 : ℕ) : ℂ))
        = w^(1+k) := by
      rw [hw, ← Complex.exp_nat_mul]; congr 1; ring
    rw [e] at h
    push_cast at h ⊢
    exact h
  have hS1 := vanish_aux m f (by omega) 1
  have hS2 := vanish_aux m g (by omega) 1
  have hS : ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m-k) * (m.choose k:ℂ) * (O + z * w^(1+k)) = 0 := by
    have h2 : ∀ k ∈ Finset.range (m+1),
        (-1:ℂ)^(m-k) * (m.choose k:ℂ) * (O + z * w^(1+k))
          = (((-1:ℝ)^(m-k) * (m.choose k:ℝ) * f.eval (1 + (k:ℝ)) : ℝ) : ℂ)
            + Complex.I * (((-1:ℝ)^(m-k) * (m.choose k:ℝ) * g.eval (1 + (k:ℝ)) : ℝ) : ℂ) := by
      intro k hk'
      rw [← hpt k hk']
      push_cast; ring
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Complex.ofReal_sum, ← Complex.ofReal_sum, hS1, hS2]
    simp
  have A : ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m-k)*(m.choose k:ℂ) = 0 := by
    have h := add_pow (1:ℂ) (-1) m
    simp only [one_pow, one_mul] at h
    rw [show (1:ℂ) + -1 = 0 by ring, zero_pow (by omega)] at h
    exact h.symm
  have B : ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m-k)*(m.choose k:ℂ) * w^k = (w-1)^m := by
    have h := add_pow w (-1) m
    rw [sub_eq_add_neg, h]
    apply Finset.sum_congr rfl; intros; ring
  have C : ∀ k ∈ Finset.range (m+1), (-1:ℂ)^(m-k) * (m.choose k:ℂ) * (O + z * w^(1+k))
      = O * ((-1:ℂ)^(m-k)*(m.choose k:ℂ)) + z * w * ((-1:ℂ)^(m-k)*(m.choose k:ℂ) * w^k) := by
    intro k _; ring
  rw [Finset.sum_congr rfl C, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, A, B] at hS
  simp only [mul_zero, zero_add] at hS
  have hw0 : w ≠ 0 := by rw [hw]; exact Complex.exp_ne_zero _
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have h1 : w = 1 := sub_eq_zero.mp h
    rw [hw, Complex.exp_eq_one_iff] at h1
    obtain ⟨t, ht⟩ := h1
    have hn : ((m+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m+1 ≠ 0)
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : Complex.I * 2 * Real.pi = (t * (2 * Real.pi * Complex.I)) * ((m+1 : ℕ) : ℂ) := by
      rw [← ht]; field_simp
    have e2 : (2 * Real.pi * Complex.I) * (1 - t * ((m+1 : ℕ) : ℂ)) = 0 := by
      linear_combination e
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
    have e3 : (1:ℂ) - t * ((m+1 : ℕ) : ℂ) = 0 := (mul_eq_zero.mp e2).resolve_left hne
    have h2 : ((t * ((m+1:ℕ):ℤ) : ℤ) : ℂ) = ((1:ℤ):ℂ) := by
      push_cast at e3 ⊢; linear_combination -e3
    have h3 : t * ((m+1:ℕ):ℤ) = 1 := by exact_mod_cast h2
    have h4 : (2:ℤ) ≤ ((m+1:ℕ):ℤ) := by push_cast; omega
    rcases le_or_gt t 0 with ht0 | ht0 <;> nlinarith
  rcases mul_eq_zero.mp hS with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hz0 h'
    · exact hw0 h'
  · exact pow_ne_zero _ hw1 h
