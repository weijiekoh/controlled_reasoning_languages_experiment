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
(∃ P : Finset.range k → Polynomial ℝ, ∀ n : ℤ, ⌊(n : ℝ) / k⌋ ^ k = ∑ i : Finset.range k, (P i).eval (n : ℝ) * ⌊(n : ℝ) / k⌋ ^ (i : ℕ)) := by
  classical
  set F : ℕ → Polynomial (Polynomial ℝ) := fun j =>
    (Polynomial.X : Polynomial (Polynomial ℝ)) -
      Polynomial.C (Polynomial.C (1 / (k:ℝ)) * (Polynomial.X - Polynomial.C (j:ℝ))) with hFdef
  have hFm : ∀ j, (F j).Monic := fun j => by
    rw [hFdef]
    exact Polynomial.monic_X_sub_C _
  obtain ⟨h, hhdef⟩ : ∃ h : Polynomial (Polynomial ℝ), h = ∏ j ∈ Finset.range k, F j := ⟨_, rfl⟩
  have hmon : h.Monic := by
    rw [hhdef]; exact Polynomial.monic_prod_of_monic _ _ (fun j _ => hFm j)
  have hdegh : h.natDegree = k := by
    have hd : ∀ j : ℕ, (F j).natDegree = 1 := fun j => by
      rw [hFdef]; exact Polynomial.natDegree_X_sub_C _
    rw [hhdef, Polynomial.natDegree_prod_of_monic _ _ (fun j _ => hFm j)]
    simp [hd]
  obtain ⟨s, hsdef⟩ : ∃ s, s = (Polynomial.X : Polynomial (Polynomial ℝ)) ^ k %ₘ h := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = (Polynomial.X : Polynomial (Polynomial ℝ)) ^ k /ₘ h := ⟨_, rfl⟩
  have hdiv : h * q + s = (Polynomial.X : Polynomial (Polynomial ℝ)) ^ k := by
    have H := Polynomial.modByMonic_add_div ((Polynomial.X : Polynomial (Polynomial ℝ)) ^ k) h
    rw [← hsdef, ← hqdef] at H
    rw [add_comm]
    exact H
  have hsdeg : s.natDegree < k := by
    by_cases hs0 : s = 0
    · simp [hs0, kpos]
    · rw [← hdegh]
      apply (Polynomial.natDegree_lt_iff_degree_lt hs0).2
      rw [← Polynomial.degree_eq_natDegree hmon.ne_zero, hsdef]
      exact Polynomial.degree_modByMonic_lt _ hmon
  have hkey : ∀ n m : ℤ, k * m ≤ n → n < k * m + k →
      (m:ℝ)^k = ∑ i ∈ Finset.range k, (s.coeff i).eval (n:ℝ) * (m:ℝ)^i := by
    intro n m h1 h2
    let phi : Polynomial (Polynomial ℝ) →+* ℝ :=
      (Polynomial.evalRingHom (m:ℝ)).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom (n:ℝ)))
    have hphiF : ∀ j : ℕ, phi (F j) = (m:ℝ) - 1 / (k:ℝ) * ((n:ℝ) - j) := by
      intro j
      simp [phi, hFdef]
    have hphih : phi h = 0 := by
      have hj0 : (n - k * m).toNat < k := by omega
      rw [hhdef, map_prod]
      apply Finset.prod_eq_zero (Finset.mem_range.2 hj0)
      rw [hphiF]
      have h3 : ((n - k*m).toNat : ℤ) = n - k*m := Int.toNat_of_nonneg (by omega)
      have hc : ((n - k*m).toNat : ℝ) = (n:ℝ) - (k:ℝ) * (m:ℝ) := by
        have h4 := congrArg (fun z : ℤ => (z:ℝ)) h3
        push_cast at h4
        linarith
      rw [hc]
      have hkpos : (k:ℝ) ≠ 0 := by positivity
      field_simp
      ring
    have hY : phi ((Polynomial.X : Polynomial (Polynomial ℝ)) ^ k) = (m:ℝ)^k := by
      simp [phi]
    have hs : phi s = ∑ i ∈ Finset.range k, (s.coeff i).eval (n:ℝ) * (m:ℝ)^i := by
      conv_lhs => rw [Polynomial.as_sum_range' s k hsdeg]
      simp [phi, map_sum]
    have := congrArg phi hdiv
    rw [map_add, map_mul, hphih, zero_mul, zero_add, hY] at this
    rw [← hs, this]
  refine ⟨fun i => s.coeff (i:ℕ), fun n => ?_⟩
  have hk : (0:ℝ) < k := by exact_mod_cast kpos
  have hfl1 := Int.floor_le ((n:ℝ)/k)
  have hfl2 := Int.lt_floor_add_one ((n:ℝ)/k)
  set m := ⌊(n:ℝ)/k⌋ with hm
  have h1 : k * m ≤ n := by
    have h5 : (m:ℝ) * k ≤ n := by
      rwa [le_div_iff₀ hk] at hfl1
    have h6 : ((k * m : ℤ):ℝ) ≤ ((n:ℤ):ℝ) := by push_cast; linarith
    exact_mod_cast h6
  have h2 : n < k * m + k := by
    have h5 : (n:ℝ) < ((m:ℝ) + 1) * k := by
      rwa [div_lt_iff₀ hk] at hfl2
    have h6 : ((n:ℤ):ℝ) < ((k * m + k : ℤ):ℝ) := by push_cast; linarith
    exact_mod_cast h6
  rw [Finset.sum_coe_sort (Finset.range k) (fun i => (s.coeff i).eval (n:ℝ) * (m:ℝ)^i)]
  exact hkey n m h1 h2
