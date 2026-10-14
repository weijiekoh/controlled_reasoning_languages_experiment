import Mathlib

open Set Nat Function

/--
Let $k$ be a positive integer. Prove that there exist polynomials $P_0(n), P_1(n), \dots, P_{k-1}(n)$ (which may depend on $k$) such that for any integer $n$,
\[
\left\lfloor \frac{n}{k} \right\rfloor^k = P_0(n) + P_1(n) \left\lfloor
\frac{n}{k} \right\rfloor + \cdots + P_{k-1}(n) \left\lfloor \frac{n}{k}
\right\rfloor^{k-1}.
\]
($\lfloor a \rfloor$ means the largest integer $\leq a$.)
-/
theorem putnam_2007_b5
(k : ℕ) (kpos : k > 0) :
(∃ P : Finset.range k → Polynomial ℝ, ∀ n : ℤ, ⌊(n : ℝ) / k⌋ ^ k = ∑ i : Finset.range k, (P i).eval (n : ℝ) * ⌊(n : ℝ) / k⌋ ^ (i : ℕ)) :=
by
  classical
  let L : ℕ → Polynomial (Polynomial ℝ) := fun s =>
    Polynomial.C (Polynomial.X - Polynomial.C (s:ℝ)) - Polynomial.C (Polynomial.C (k:ℝ)) * Polynomial.X
  have hLdeg : ∀ s, (L s).natDegree ≤ 1 := by
    intro s
    simp only [L]
    compute_degree!
  have hL1 : ∀ s, (L s).coeff 1 = -Polynomial.C (k:ℝ) := by
    intro s
    simp only [L, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one]
    simp
  have hG : ∀ s, (∏ j ∈ Finset.range s, L j).natDegree ≤ s ∧
      (∏ j ∈ Finset.range s, L j).coeff s = (-Polynomial.C (k:ℝ))^s := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Finset.prod_range_succ]
      constructor
      · exact (Polynomial.natDegree_mul_le).trans (by have := hLdeg s; omega)
      · have h := Polynomial.coeff_mul_add_eq_of_natDegree_le ih.1 (hLdeg s)
        rw [h, ih.2, hL1, pow_succ]
  set G : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k, L j with hGdef
  have hGdeg : G.natDegree < k + 1 := Nat.lt_succ_of_le (hG k).1
  have hGk : G.coeff k = (-Polynomial.C (k:ℝ))^k := (hG k).2
  have hc : (-(k:ℝ))^k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr (by positivity))
  have key : ∀ n : ℤ, ∑ i ∈ Finset.range k,
      (G.coeff i).eval (n:ℝ) * (⌊(n:ℝ)/k⌋ : ℝ)^i + (-(k:ℝ))^k * (⌊(n:ℝ)/k⌋ : ℝ)^k = 0 := by
    intro n
    set m := ⌊(n:ℝ)/k⌋ with hm
    have hkpos : (0:ℝ) < k := by exact_mod_cast kpos
    have hb1 : ((m:ℤ):ℝ) ≤ (n:ℝ)/k := Int.floor_le _
    have hb2 : (n:ℝ)/k < (m:ℝ) + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ hkpos] at hb1
    rw [div_lt_iff₀ hkpos] at hb2
    have i1 : (k:ℤ) * m ≤ n := by
      have : ((k:ℤ) * m : ℝ) ≤ (n:ℝ) := by push_cast; linarith
      exact_mod_cast this
    have i2 : (n:ℤ) < (k:ℤ) * m + k := by
      have : (n:ℝ) < ((k:ℤ) * m + k : ℝ) := by push_cast; nlinarith
      exact_mod_cast this
    set j := (n - k * m).toNat with hj
    have hjk : j < k := by omega
    have hjv : ((j:ℕ):ℤ) = n - k * m := by omega
    have hφ : Polynomial.eval₂ (Polynomial.evalRingHom (n:ℝ)) (m:ℝ) G = 0 := by
      rw [hGdef, Polynomial.eval₂_finsetProd]
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hjk)
      simp only [L]
      simp
      have : ((j:ℕ):ℝ) = (n:ℝ) - (k:ℝ) * (m:ℝ) := by
        have := congrArg (fun z : ℤ => (z:ℝ)) hjv
        push_cast at this; linarith
      linarith
    rw [Polynomial.eval₂_eq_sum_range' _ hGdeg, Finset.sum_range_succ, hGk] at hφ
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_neg,
      Polynomial.eval_C] at hφ
    exact hφ
  refine ⟨fun i => Polynomial.C (((-(k:ℝ))^k)⁻¹) * -(G.coeff (i:ℕ)), ?_⟩
  intro n
  rw [Finset.sum_coe_sort (Finset.range k)
    (fun i => (Polynomial.C (((-(k:ℝ))^k)⁻¹) * -(G.coeff i)).eval (n:ℝ) * (⌊(n:ℝ)/k⌋ : ℝ)^i)]
  have hk := key n
  have hsum : ∑ i ∈ Finset.range k,
      (Polynomial.C (((-(k:ℝ))^k)⁻¹) * -(G.coeff i)).eval (n:ℝ) * (⌊(n:ℝ)/k⌋ : ℝ)^i
      = ((-(k:ℝ))^k)⁻¹ * -(∑ i ∈ Finset.range k, (G.coeff i).eval (n:ℝ) * (⌊(n:ℝ)/k⌋ : ℝ)^i) := by
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_neg]
    ring
  rw [hsum]
  have hS : ∑ i ∈ Finset.range k, (G.coeff i).eval (n:ℝ) * (⌊(n:ℝ)/k⌋ : ℝ)^i
      = -((-(k:ℝ))^k * (⌊(n:ℝ)/k⌋ : ℝ)^k) := by linarith
  rw [hS]
  field_simp
