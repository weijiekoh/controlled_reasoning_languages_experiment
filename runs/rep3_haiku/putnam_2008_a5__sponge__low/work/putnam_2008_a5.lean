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
  push_neg at hcon
  obtain ⟨O, z, hz, hk⟩ := hfg
  obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω = Complex.exp (Complex.I * 2 * Real.pi / n) := ⟨_, rfl⟩
  have hF : ∀ x : ℝ, (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).eval (x:ℂ) = f.eval x + Complex.I * g.eval x := by
    intro x
    have e : ∀ p : Polynomial ℝ, Polynomial.eval₂ Complex.ofRealHom (x:ℂ) p = ((p.eval x:ℝ):ℂ) := fun p => Polynomial.eval₂_at_apply Complex.ofRealHom x
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, e]
  have hdeg : (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).natDegree < n - 1 := by
    have h1 := Polynomial.natDegree_add_le (Polynomial.map Complex.ofRealHom f) (Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g)
    have h2 := Polynomial.natDegree_C_mul_le Complex.I (Polynomial.map Complex.ofRealHom g)
    have h3 : (Polynomial.map Complex.ofRealHom f).natDegree ≤ f.natDegree := Polynomial.natDegree_map_le
    have h4 : (Polynomial.map Complex.ofRealHom g).natDegree ≤ g.natDegree := Polynomial.natDegree_map_le
    omega
  have hzero := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg
  have key := congrFun hzero 1
  rw [fwdDiff_iter_eq_sum_shift, show n - 1 + 1 = n by omega] at key
  simp only [zsmul_eq_mul] at key
  simp only [Pi.zero_apply] at key
  have hval : ∀ k ∈ Finset.range n, (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).eval (1 + (k:ℂ)) = O + z * ω ^ (k+1) := by
    intro k hkm
    have hm := Finset.mem_range.mp hkm
    have h1 := hk (k+1) (by simp only [Set.mem_Icc]; omega)
    have h2 : (1 + (k:ℂ)) = (((k+1:ℕ):ℝ):ℂ) := by push_cast; ring
    rw [h2, hF, h1, hω, ← Complex.exp_nat_mul]
    congr 3
    push_cast
    ring
  have key2 : ∑ k ∈ Finset.range n, ((-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) * (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).eval (1 + (k:ℂ)) = 0 := by
    have e : ∑ k ∈ Finset.range n, ((-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) * (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).eval (1 + (k:ℂ)) = ∑ k ∈ Finset.range n, (((((-1:ℤ)^(n-1-k) * ((n-1).choose k : ℤ)) : ℤ) : ℂ)) * (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).eval (1 + k • (1:ℂ)) := Finset.sum_congr rfl (fun k _ => by (try simp only [nsmul_eq_mul, mul_one]); push_cast; ring)
    rw [e]
    exact key
  have e2 : ∑ k ∈ Finset.range n, ((-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) * (Polynomial.map Complex.ofRealHom f + Polynomial.C Complex.I * Polynomial.map Complex.ofRealHom g).eval (1 + (k:ℂ)) = ∑ k ∈ Finset.range n, ((-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) * (O + z * ω ^ (k+1)) :=
    Finset.sum_congr rfl (fun k hkm => by rw [hval k hkm])
  rw [e2] at key2
  have hS : ∑ k ∈ Finset.range n, ((-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) * (O + z * ω ^ (k+1)) = O * (∑ k ∈ Finset.range n, (-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) + z * ω * (∑ k ∈ Finset.range n, ω^k * (-1:ℂ)^(n-1-k) * ((n-1).choose k : ℂ)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hS] at key2
  have hA := add_pow (1:ℂ) (-1) (n-1)
  rw [show n - 1 + 1 = n by omega] at hA
  have hA0 : (1:ℂ) + -1 = 0 := by ring
  rw [hA0, zero_pow (by omega)] at hA
  simp only [one_pow, one_mul] at hA
  have hB := add_pow ω (-1) (n-1)
  rw [show n - 1 + 1 = n by omega] at hB
  have hne : ω ≠ 1 := by
    intro h1
    rw [hω] at h1
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
    have hn : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [div_eq_iff hn] at hm
    have h4 : ((m:ℂ) * n - 1) * (2 * Real.pi * Complex.I) = 0 := by
      linear_combination (-1:ℂ) * hm
    rcases mul_eq_zero.mp h4 with h5 | h5
    · have h6 : ((m * (n:ℤ) : ℤ) : ℂ) = 1 := by
        push_cast
        linear_combination h5
      have h7 : m * (n:ℤ) = 1 := by exact_mod_cast h6
      have h8 : (3:ℤ) ≤ n := by omega
      have hm1 : m ≥ 1 ∨ m ≤ -1 := by
        by_contra hc
        have hm0 : m = 0 := by omega
        subst hm0
        simp at h7
      rcases hm1 with h | h <;> nlinarith
    · exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero h5
  have hω0 : ω ≠ 0 := by rw [hω]; exact Complex.exp_ne_zero _
  have hfin : z * ω * (ω + -1)^(n-1) = 0 := by
    linear_combination key2 + O * hA + z * ω * hB
  rcases mul_eq_zero.mp hfin with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hz h
    · exact hω0 h
  · exact pow_ne_zero _ (fun h' => hne (by linear_combination h')) h
