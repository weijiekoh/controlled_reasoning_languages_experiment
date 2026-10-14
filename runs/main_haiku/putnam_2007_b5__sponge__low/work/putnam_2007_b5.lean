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
  have hkR : (0:ℝ) < k := by exact_mod_cast kpos
  let f : ℕ → Polynomial (Polynomial ℝ) := fun j =>
    Polynomial.C (Polynomial.C (-(k:ℝ))) * Polynomial.X + Polynomial.C (Polynomial.X - Polynomial.C (j:ℝ))
  let Q : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k, f j
  have hdeg : ∀ j, (f j).natDegree = 1 := by
    intro j
    simp only [f]
    compute_degree!
    all_goals omega
  have hlead : ∀ j, (f j).leadingCoeff = Polynomial.C (-(k:ℝ)) := by
    intro j
    unfold Polynomial.leadingCoeff
    rw [hdeg j]
    simp [f, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C]
  have hne : ∀ j, f j ≠ 0 := by
    intro j h
    have := hdeg j
    rw [h] at this
    simp at this
  have hQdeg : Q.natDegree = k := by
    simp only [Q]
    rw [Polynomial.natDegree_prod _ _ (fun j _ => hne j)]
    simp [hdeg]
  have hQlead : Q.leadingCoeff = (Polynomial.C (-(k:ℝ)))^k := by
    simp only [Q]
    rw [Polynomial.leadingCoeff_prod]
    simp [hlead, Finset.prod_const]
  have hk : Q.coeff k = (Polynomial.C (-(k:ℝ)))^k := by
    have := hQlead
    unfold Polynomial.leadingCoeff at this
    rwa [hQdeg] at this
  have hev : ∀ x y : ℝ, (Q.map (Polynomial.evalRingHom x)).eval y
      = ∏ j ∈ Finset.range k, (x - j - k*y) := by
    intro x y
    simp [Q, f, Polynomial.eval_map, Polynomial.eval₂_finsetProd]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    ring
  have hc : (-(k:ℝ))^k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hkR.ne')
  refine ⟨fun i => Polynomial.C (-(((-(k:ℝ))^k)⁻¹)) * Q.coeff (i:ℕ), ?_⟩
  intro n
  set m : ℤ := ⌊(n:ℝ)/k⌋ with hm
  have h1 : (m:ℝ) * k ≤ n := (le_div_iff₀ hkR).mp (Int.floor_le _)
  have h2 : (n:ℝ) < (m + 1) * k := (div_lt_iff₀ hkR).mp (Int.lt_floor_add_one _)
  have h1' : m * k ≤ n := by exact_mod_cast h1
  have h2' : n < (m + 1) * k := by exact_mod_cast h2
  have hprod : ∏ j ∈ Finset.range k, ((n:ℝ) - j - k*(m:ℝ)) = 0 := by
    have hj : (((n - k*m).toNat : ℕ) : ℤ) = n - k*m := Int.toNat_of_nonneg (by linarith)
    have hjk : (n - k*m).toNat < k := by
      have : (((n - k*m).toNat : ℕ) : ℤ) < (k:ℤ) := by rw [hj]; nlinarith
      exact_mod_cast this
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hjk)
    have h3 : ((((n - k*m).toNat : ℕ) : ℤ) : ℝ) = ((n - k*m : ℤ) : ℝ) := by rw [hj]
    push_cast at h3
    linarith
  have hlt : (Q.map (Polynomial.evalRingHom (n:ℝ))).natDegree < k+1 :=
    lt_of_le_of_lt Polynomial.natDegree_map_le (by omega)
  have hS := Polynomial.eval_eq_sum_range' hlt (m:ℝ)
  rw [hev, hprod, Finset.sum_range_succ] at hS
  simp only [Polynomial.coeff_map] at hS
  rw [hk] at hS
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_C] at hS
  simp only [Finset.sum_coe_sort (Finset.range k) (fun i : ℕ => Polynomial.eval (n:ℝ)
    (Polynomial.C (-(((-(k:ℝ))^k)⁻¹)) * Q.coeff i) * (m:ℝ)^i)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hsum : ∑ i ∈ Finset.range k, -(((-(k:ℝ))^k)⁻¹) * Polynomial.eval (n:ℝ) (Q.coeff i) * (m:ℝ)^i
      = -(((-(k:ℝ))^k)⁻¹) * ∑ i ∈ Finset.range k, Polynomial.eval (n:ℝ) (Q.coeff i) * (m:ℝ)^i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [hsum]
  have hS2 : ∑ i ∈ Finset.range k, Polynomial.eval (n:ℝ) (Q.coeff i) * (m:ℝ)^i
      = -((-(k:ℝ))^k * (m:ℝ)^k) := by linarith
  rw [hS2]
  field_simp
