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
  open Polynomial in
    by_contra h
    push_neg at h
    obtain ⟨O, z, hz, H⟩ := hfg
    obtain ⟨P, hP⟩ : ∃ P : ℂ[X], P = f.map Complex.ofRealHom + C Complex.I * g.map Complex.ofRealHom := ⟨_, rfl⟩
    have hdeg : P.natDegree < n - 1 := by
      have h1 : (f.map Complex.ofRealHom).natDegree ≤ f.natDegree := natDegree_map_le
      have h2 : (C Complex.I * g.map Complex.ofRealHom).natDegree ≤ g.natDegree :=
        (natDegree_C_mul_le _ _).trans natDegree_map_le
      have h3 : P.natDegree ≤ _ := hP ▸ natDegree_add_le (f.map Complex.ofRealHom) (C Complex.I * g.map Complex.ofRealHom)
      omega
    have h0 := congrFun (fwdDiff_iter_eq_zero_of_degree_lt hdeg) 1
    rw [fwdDiff_iter_eq_sum_shift] at h0
    set ω : ℂ := Complex.exp (Complex.I * 2 * Real.pi / n) with hω
    have hval : ∀ k ∈ Finset.range (n - 1 + 1),
        ((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) * eval (1 + (k:ℂ)) P
        = ((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) * O + (z * ω) * (((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) * ω ^ k) := by
      intro k hk
      have hk' : k + 1 ∈ Set.Icc 1 n := by
        simp at hk; constructor <;> omega
      have := H (k+1) hk'
      have e : eval (1 + (k:ℂ)) P = f.eval ((k+1:ℕ):ℝ) + Complex.I * g.eval ((k+1:ℕ):ℝ) := by
        simp [hP, eval_map, ← Polynomial.eval₂_at_apply]
        rw [show (1+(k:ℂ)) = Complex.ofRealHom ((k:ℝ)+1) by simp [add_comm], eval₂_at_apply, eval₂_at_apply]
        simp
      have e2 : Complex.exp (Complex.I * 2 * Real.pi * ((k+1:ℕ):ℂ) / n) = ω ^ (k+1) := by
        rw [hω, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
      rw [e, this]
      push_cast at e2 ⊢
      rw [e2]; ring
    have hprim : IsPrimitiveRoot ω n := by
      have := Complex.isPrimitiveRoot_exp n (by omega)
      rwa [hω, show Complex.I * 2 * Real.pi / n = 2 * Real.pi * Complex.I / n by ring]
    have hω1 : ω - 1 ≠ 0 := sub_ne_zero.mpr (hprim.ne_one (by omega))
    have hω0 : ω ≠ 0 := hprim.ne_zero (by omega)
    simp only [Pi.zero_apply, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, nsmul_eq_mul, mul_one] at h0
    rw [Finset.sum_congr rfl hval, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at h0
    have S1 : ∑ k ∈ Finset.range (n - 1 + 1), (-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ) = 0 := by
      have := add_pow (1:ℂ) (-1) (n-1)
      rw [show (1:ℂ) + -1 = 0 by norm_num, zero_pow (by omega)] at this
      rw [this]; apply Finset.sum_congr rfl; intro k _; simp
    have S2 : ∑ k ∈ Finset.range (n - 1 + 1), ((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) * ω ^ k = (ω - 1) ^ (n-1) := by
      rw [sub_eq_add_neg, add_pow]; apply Finset.sum_congr rfl; intro k _; ring
    rw [S1, S2, zero_mul, zero_add] at h0
    exact mul_ne_zero (mul_ne_zero hz hω0) (pow_ne_zero _ hω1) h0
