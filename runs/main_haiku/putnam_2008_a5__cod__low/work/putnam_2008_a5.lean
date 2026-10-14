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
  have aux_alg : ∀ (m : ℕ), m ≠ 0 → ∀ (ω O z : ℂ), z ≠ 0 → ω ≠ 0 → ω ≠ 1 →
      ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (O + z * ω^(k+1)) ≠ 0 := by
    intro m hm ω O z hz hω hω1
    have e1 : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) = 0 := by
      have := add_pow (1:ℂ) (-1) m
      simp only [one_pow, one_mul] at this
      rw [show (1:ℂ) + -1 = 0 by ring, zero_pow hm] at this
      exact this.symm
    have e2 : ∑ k ∈ Finset.range (m+1), ω^k * ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) = (ω + -1)^m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intros; ring
    have hsplit : ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) * (O + z * ω^(k+1))
        = O * ∑ k ∈ Finset.range (m+1), ((-1:ℂ)^(m-k) * (m.choose k : ℂ))
          + z * ω * ∑ k ∈ Finset.range (m+1), ω^k * ((-1:ℂ)^(m-k) * (m.choose k : ℂ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros; ring
    have hne : (ω + -1)^m ≠ 0 := pow_ne_zero _ (by intro h; apply hω1; linear_combination h)
    rw [hsplit, e1, e2, mul_zero, zero_add]
    exact mul_ne_zero (mul_ne_zero hz hω) hne
  by_contra hcon
  push_neg at hcon
  obtain ⟨hf, hg⟩ := hcon
  obtain ⟨O, z, hz, hk⟩ := hfg
  have hprim := Complex.isPrimitiveRoot_exp n (by omega)
  set ω : ℂ := Complex.exp (2 * (Real.pi:ℂ) * Complex.I / (n:ℂ)) with hωdef
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  have hω1 : ω ≠ 1 := hprim.ne_one (by omega)
  have hpow : ∀ j : ℕ, Complex.exp (Complex.I * 2 * Real.pi * j / n) = ω ^ j := by
    intro j
    rw [hωdef, ← Complex.exp_nat_mul]
    congr 1; ring
  have hk' : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (f.eval (k:ℝ)) + Complex.I * (g.eval (k:ℝ)) = O + z * ω^k := by
    intro k h1 h2
    rw [hk k ⟨h1, h2⟩, hpow]
  set P : ℕ → ℂ := fun k => ((f.coeff k : ℝ) : ℂ) + Complex.I * ((g.coeff k : ℝ) : ℂ) with hP
  have hG : ∀ x : ℝ, ((f.eval x : ℝ) : ℂ) + Complex.I * ((g.eval x : ℝ) : ℂ)
      = ∑ k ∈ Finset.range (n-1), P k * (x:ℂ)^k := by
    intro x
    rw [Polynomial.eval_eq_sum_range' (show f.natDegree < n-1 by omega) x,
      Polynomial.eval_eq_sum_range' (show g.natDegree < n-1 by omega) x]
    push_cast
    simp only [hP, Finset.mul_sum, add_mul, Finset.sum_add_distrib, mul_assoc]
  set G : ℂ → ℂ := fun r => ∑ k ∈ Finset.range (n-1), P k * r^k with hGdef
  have hzero : (fwdDiff 1)^[n-1] G = 0 := fwdDiff_iter_sum_mul_pow_eq_zero (n := n-1) P
  have key := congrFun hzero 1
  rw [fwdDiff_iter_eq_sum_shift] at key
  have hGv : ∀ k ∈ Finset.range (n-1+1), G (1 + k • (1:ℂ)) = O + z * ω^(k+1) := by
    intro k hk0
    have hk0' := Finset.mem_range.1 hk0
    have hx : (1:ℂ) + k • (1:ℂ) = (((k+1:ℕ):ℝ):ℂ) := by
      simp only [nsmul_eq_mul, mul_one]; push_cast; ring
    rw [hx, hGdef]
    simp only
    rw [← hG]
    exact hk' (k+1) (by omega) (by omega)
  rw [Finset.sum_congr rfl (fun k hk0 => by rw [hGv k hk0])] at key
  simp only [zsmul_eq_mul] at key
  push_cast at key
  exact aux_alg (n-1) (by omega) ω O z hz hω0 hω1 key
