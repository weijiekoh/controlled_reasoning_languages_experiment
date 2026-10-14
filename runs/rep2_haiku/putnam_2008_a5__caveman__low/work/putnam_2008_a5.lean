import Mathlib

open Filter Topology Set

theorem putnam_2008_a5
(n : ℕ)
(nge3 : n ≥ 3)
(f g : Polynomial ℝ)
(hfg : ∃ O z : ℂ, z ≠ 0 ∧ ∀ k : ℕ, k ∈ Icc 1 n → (f.eval (k : ℝ)) + Complex.I * (g.eval (k : ℝ)) = O + z * Complex.exp (Complex.I * 2 * Real.pi * k / n))
: (f.natDegree ≥ n - 1 ∨ g.natDegree ≥ n - 1) := by
  obtain ⟨O, z, hz, h⟩ := hfg
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = Complex.exp (Complex.I * 2 * Real.pi / n) := ⟨_, rfl⟩
  have hpow : ∀ k : ℕ, Complex.exp (Complex.I * 2 * Real.pi * k / n) = ω ^ k := by
    intro k
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [hω, Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have e : (Complex.I * 2 * Real.pi / n) * n = Complex.I * 2 * Real.pi :=
      div_mul_cancel₀ _ hn0
    rw [hm] at e
    have h3 : ((m : ℂ) * n - 1) * (2 * Real.pi * Complex.I) = 0 := by
      linear_combination e
    rcases mul_eq_zero.1 h3 with h4 | h4
    · have h6 : ((m * n : ℤ) : ℂ) = 1 := by
        push_cast
        linear_combination h4
      have h7 : m * (n : ℤ) = 1 := by exact_mod_cast h6
      have h8 : (3 : ℤ) ≤ n := by exact_mod_cast nge3
      rcases le_or_gt m 0 with hm0 | hm0
      · nlinarith
      · nlinarith
    · exact absurd h4 (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  have hω0 : ω ≠ 0 := by rw [hω]; exact Complex.exp_ne_zero _
  by_contra hcon
  push_neg at hcon
  obtain ⟨hf, hg⟩ := hcon
  set F : Polynomial ℂ :=
    (f.map Complex.ofRealHom) + Polynomial.C Complex.I * (g.map Complex.ofRealHom)
      - Polynomial.C O with hFdef
  have h1 : (f.map Complex.ofRealHom).natDegree < n - 1 :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hf
  have h2 : (g.map Complex.ofRealHom).natDegree < n - 1 :=
    lt_of_le_of_lt Polynomial.natDegree_map_le hg
  have h3 : (Polynomial.C Complex.I * (g.map Complex.ofRealHom)).natDegree < n - 1 :=
    lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) h2
  have h4 : ((f.map Complex.ofRealHom) + Polynomial.C Complex.I * (g.map Complex.ofRealHom)).natDegree < n - 1 :=
    lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt h1 h3)
  have hF : F.natDegree < n - 1 := by
    rw [hFdef, Polynomial.natDegree_sub_C]
    exact h4
  have hev : ∀ k : ℕ, k ∈ Icc 1 n → F.eval (k : ℂ) = z * ω ^ k := by
    intro k hk
    have hk' := h k hk
    rw [hpow k] at hk'
    rw [hFdef]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_natCast_map]
    have : ((f.eval (k : ℝ) : ℝ) : ℂ) + Complex.I * ((g.eval (k : ℝ) : ℝ) : ℂ) = O + z * ω ^ k := hk'
    simp only [Complex.ofRealHom_eq_coe] at *
    linear_combination this
  have hfun : (fun r : ℂ => F.eval r) = fun r => ∑ k ∈ Finset.range (n - 1), F.coeff k * r ^ k :=
    funext (fun r => Polynomial.eval_eq_sum_range' hF r)
  have hzero : (fwdDiff 1)^[n - 1] (fun r : ℂ => F.eval r) = 0 := by
    rw [hfun]
    exact fwdDiff_iter_sum_mul_pow_eq_zero _
  have key := congrFun hzero 1
  rw [fwdDiff_iter_eq_sum_shift] at key
  have key2 : ∑ k ∈ Finset.range (n - 1 + 1),
      ((-1 : ℤ) ^ (n - 1 - k) * ↑((n - 1).choose k)) • (z * ω ^ (k + 1)) = 0 := by
    refine Eq.trans ?_ key
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n - 1 + 1 := Finset.mem_range.1 hk
    rw [show k • (1 : ℂ) = ((k : ℕ) : ℂ) by simp]
    rw [show (1 : ℂ) + (k : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring]
    rw [hev (k + 1) (Set.mem_Icc.2 ⟨by omega, by omega⟩)]
  have key3 : ∑ k ∈ Finset.range (n - 1 + 1),
      ((-1 : ℤ) ^ (n - 1 - k) * ↑((n - 1).choose k)) • (z * ω ^ (k + 1))
        = z * ω * (ω - 1) ^ (n - 1) := by
    rw [show (ω - 1) ^ (n - 1) = (ω + -1) ^ (n - 1) by ring, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    ring
  have hne : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
  have := key2
  rw [key3] at this
  exact mul_ne_zero (mul_ne_zero hz hω0) (pow_ne_zero _ hne) this
