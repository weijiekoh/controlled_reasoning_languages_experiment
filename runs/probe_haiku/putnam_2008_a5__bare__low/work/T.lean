import Mathlib

open Filter Topology Set

theorem putnam_2008_a5
(n : ℕ)
(nge3 : n ≥ 3)
(f g : Polynomial ℝ)
(hfg : ∃ O z : ℂ, z ≠ 0 ∧ ∀ k : ℕ, k ∈ Icc 1 n → (f.eval (k : ℝ)) + Complex.I * (g.eval (k : ℝ)) = O + z * Complex.exp (Complex.I * 2 * Real.pi * k / n))
: (f.natDegree ≥ n - 1 ∨ g.natDegree ≥ n - 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨O, z, hz, hO⟩ := hfg
  obtain ⟨m, hm⟩ : ∃ m, m = n - 1 := ⟨_, rfl⟩
  set H : Polynomial ℂ := f.map (algebraMap ℝ ℂ) + Polynomial.C Complex.I * g.map (algebraMap ℝ ℂ) with hH
  have hHeval : ∀ k : ℕ, H.eval (k:ℂ) = ((Polynomial.eval (k:ℝ) f : ℝ) : ℂ) + Complex.I * ((Polynomial.eval (k:ℝ) g : ℝ) : ℂ) := by
    intro k
    simp only [hH, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_natCast_map]
    simp
  have hHd : H.natDegree < m := by
    rw [hm]
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt Polynomial.natDegree_map_le hf
    · exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (lt_of_le_of_lt Polynomial.natDegree_map_le hg)
  have hzero := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (R := ℂ) hHd
  have h0 := congrFun hzero 1
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simp only [Pi.zero_apply] at h0
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = Complex.exp (2 * Real.pi * Complex.I / (n:ℂ)) := ⟨_, rfl⟩
  have hprim : IsPrimitiveRoot ω n := by
    rw [hω]; exact Complex.isPrimitiveRoot_exp n (by omega)
  have hω1 : ω - 1 ≠ 0 := sub_ne_zero.mpr (hprim.ne_one (by omega))
  have hterm : ∀ k ∈ Finset.range (m+1), ((-1:ℤ)^(m-k) * (m.choose k : ℤ)) • H.eval ((1:ℂ) + (k:ℕ) • (1:ℂ))
      = ((-1:ℤ)^(m-k) * (m.choose k : ℤ)) • (O + z * ω^(k+1)) := by
    intro k hk
    have hk' : k < m + 1 := Finset.mem_range.mp hk
    have hk1 : (1:ℂ) + (k:ℕ) • (1:ℂ) = ((k+1 : ℕ) : ℂ) := by
      rw [nsmul_eq_mul]; push_cast; ring
    have hmem : (k+1) ∈ Icc 1 n := by
      constructor <;> omega
    have hO' := hO (k+1) hmem
    have hexp : Complex.exp (Complex.I * 2 * Real.pi * ((k+1 : ℕ) : ℂ) / n) = ω^(k+1) := by
      rw [hω, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hk1, hHeval]
    rw [hexp] at hO'
    push_cast at hO' ⊢
    rw [hO']
  have hsum : ∑ k ∈ Finset.range (m+1), ((-1:ℤ)^(m-k) * (m.choose k : ℤ)) • (O + z * ω^(k+1)) = 0 := by
    rw [← h0]
    exact (Finset.sum_congr rfl hterm).symm
  sorry
