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
  let G : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (Polynomial.C (1/(k:ℝ)) * (Polynomial.X - Polynomial.C (j:ℝ))))
  have hmonic : G.Monic := Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
  have hdeg : G.natDegree = k := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
    rw [Finset.sum_congr rfl (fun j _ => Polynomial.natDegree_X_sub_C _)]; simp
  have hlead : G.coeff k = 1 := by
    have := hmonic.coeff_natDegree
    rw [hdeg] at this
    exact this
  have key : ∀ n : ℤ, ∑ i ∈ Finset.range (k+1), (G.coeff i).eval (n:ℝ) * ((⌊(n:ℝ)/k⌋ : ℤ) : ℝ)^i = 0 := by
    intro n
    have hkpos : (0:ℝ) < k := by exact_mod_cast kpos
    have h1 : ((⌊(n:ℝ)/k⌋ : ℤ) : ℝ) ≤ (n:ℝ)/k := Int.floor_le _
    have h2 : (n:ℝ)/k < ((⌊(n:ℝ)/k⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    generalize ⌊(n:ℝ)/k⌋ = m at h1 h2 ⊢
    have h1' : (m:ℝ) * k ≤ n := (le_div_iff₀ hkpos).mp h1
    have h2' : (n:ℝ) < (m+1) * k := (div_lt_iff₀ hkpos).mp h2
    have h1'' : m * (k:ℤ) ≤ n := by exact_mod_cast h1'
    have h2'' : n < (m+1) * (k:ℤ) := by exact_mod_cast h2'
    have e : (m+1) * (k:ℤ) = m*k + k := by ring
    rw [e] at h2''
    have hj0c : (((n - m*k).toNat : ℕ) : ℤ) = n - m*k := Int.toNat_of_nonneg (by linarith)
    have hj0lt : (n - m*k).toNat < k := by
      have : (((n - m*k).toNat : ℕ) : ℤ) < k := by rw [hj0c]; linarith
      exact_mod_cast this
    have hjR : (((n - m*k).toNat : ℕ) : ℝ) = (n:ℝ) - m * k := by
      have := congrArg (fun z : ℤ => (z:ℝ)) hj0c
      push_cast at this
      linarith
    have hG : G.map (Polynomial.evalRingHom (n:ℝ)) = ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C ((1/(k:ℝ)) * ((n:ℝ) - j))) := by
      simp only [G]
      rw [Polynomial.map_prod]
      apply Finset.prod_congr rfl
      intro j _
      simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hev : Polynomial.eval (m:ℝ) (G.map (Polynomial.evalRingHom (n:ℝ))) = 0 := by
      rw [hG, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (i := (n - m*k).toNat) (Finset.mem_range.mpr hj0lt)
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [hjR]
      field_simp
      ring
    have hdeg' : (G.map (Polynomial.evalRingHom (n:ℝ))).natDegree < k + 1 :=
      lt_of_le_of_lt (Polynomial.natDegree_map_le) (by rw [hdeg]; omega)
    rw [Polynomial.eval_eq_sum_range' (by omega)] at hev
    simpa [Polynomial.coeff_map] using hev
  refine ⟨fun i => -(G.coeff i), fun n => ?_⟩
  have hk := key n
  rw [Finset.sum_range_succ, hlead] at hk
  simp only [Polynomial.eval_neg, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_coe_sort (Finset.range k) (fun i => (G.coeff i).eval (n:ℝ) * ((⌊(n:ℝ)/k⌋ : ℤ) : ℝ)^i)]
  simp at hk
  linarith
