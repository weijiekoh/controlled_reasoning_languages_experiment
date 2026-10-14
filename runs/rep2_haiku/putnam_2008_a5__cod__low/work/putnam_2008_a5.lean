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
  obtain ⟨O, z, hz, hvert⟩ := hfg
  by_contra hcon
  simp only [not_or, ge_iff_le, not_le] at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℂ, P = Polynomial.map (algebraMap ℝ ℂ) f + Polynomial.C Complex.I * Polynomial.map (algebraMap ℝ ℂ) g := ⟨_, rfl⟩
  have hdeg : P.natDegree < n - 1 := by
    have h1 : (Polynomial.map (algebraMap ℝ ℂ) f).natDegree ≤ f.natDegree := Polynomial.natDegree_map_le
    have h2 : (Polynomial.map (algebraMap ℝ ℂ) g).natDegree ≤ g.natDegree := Polynomial.natDegree_map_le
    have h3 : (Polynomial.C Complex.I * Polynomial.map (algebraMap ℝ ℂ) g).natDegree ≤ g.natDegree :=
      le_trans (Polynomial.natDegree_C_mul_le _ _) h2
    have h4 := Polynomial.natDegree_add_le (Polynomial.map (algebraMap ℝ ℂ) f) (Polynomial.C Complex.I * Polynomial.map (algebraMap ℝ ℂ) g)
    rw [hP]
    omega
  have hev : ∀ m : ℕ, m ∈ Icc 1 n → P.eval (m : ℂ) = O + z * Complex.exp (Complex.I * 2 * Real.pi * m / n) := by
    intro m hm
    have := hvert m hm
    rw [← this, hP]
    simp [Polynomial.eval_add, Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C]
  have hz0 := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (R := ℂ) (P := P) (n := n - 1) hdeg
  have key := congrFun hz0 1
  simp only [Pi.zero_apply] at key
  rw [fwdDiff_iter_eq_sum_shift] at key
  set w : ℂ := Complex.exp (Complex.I * 2 * Real.pi / n) with hwdef
  have hw : ∀ m : ℕ, Complex.exp (Complex.I * 2 * Real.pi * m / n) = w ^ m := by
    intro m
    rw [hwdef, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hw1 : w - 1 ≠ 0 := by
    intro h
    have h1 : w = 1 := by linear_combination h
    rw [hwdef, Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h2 : (1 : ℂ) = (m : ℂ) * n := by
      field_simp at hm
      linear_combination hm
    have h3 : (1 : ℤ) = m * n := by exact_mod_cast h2
    have h4 : (n : ℤ) ∣ 1 := ⟨m, by linarith⟩
    have h5 := Int.le_of_dvd (by norm_num) h4
    omega
  set c : ℕ → ℂ := fun k => (-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ) with hc
  have hterm : ∑ k ∈ Finset.range (n - 1 + 1), c k * (O + z * w ^ (k + 1)) = 0 := by
    rw [← key]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n - 1 + 1 := Finset.mem_range.mp hk
    have hm : 1 + k ∈ Icc 1 n := by simp only [mem_Icc]; omega
    have e1 : (1 : ℂ) + k • (1 : ℂ) = ((1 + k : ℕ) : ℂ) := by
      simp only [nsmul_eq_mul, mul_one]; push_cast; ring
    rw [zsmul_eq_mul, hc, e1, hev _ hm, hw]
    push_cast
    ring
  have A : ∑ k ∈ Finset.range (n - 1 + 1), c k = 0 := by
    have h := add_pow (1 : ℂ) (-1) (n - 1)
    rw [show (1 : ℂ) + -1 = 0 by ring, zero_pow (by omega)] at h
    rw [show ∑ k ∈ Finset.range (n - 1 + 1), c k = ∑ k ∈ Finset.range (n - 1 + 1), (1 : ℂ) ^ k * (-1) ^ (n - 1 - k) * ((n - 1).choose k : ℂ) from Finset.sum_congr rfl (fun k _ => by rw [hc]; ring)]
    rw [← h]
  have B : ∑ k ∈ Finset.range (n - 1 + 1), c k * w ^ k = (w - 1) ^ (n - 1) := by
    have h := add_pow w (-1) (n - 1)
    rw [show w + -1 = w - 1 by ring] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro k _
    rw [hc]; ring
  have expand : ∑ k ∈ Finset.range (n - 1 + 1), c k * (O + z * w ^ (k + 1))
      = O * (∑ k ∈ Finset.range (n - 1 + 1), c k) + z * w * (∑ k ∈ Finset.range (n - 1 + 1), c k * w ^ k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [expand, A, B] at hterm
  have hpow : (w - 1) ^ (n - 1) ≠ 0 := pow_ne_zero _ hw1
  have : z * w * (w - 1) ^ (n - 1) = 0 := by linear_combination hterm
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hz h
    · exact hw0 h
  · exact hpow h
