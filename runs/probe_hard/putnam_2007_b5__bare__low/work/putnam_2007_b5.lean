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
(∃ P : Finset.range k → Polynomial ℝ, ∀ n : ℤ, ⌊(n : ℝ) / k⌋ ^ k = ∑ i : Finset.range k, (P i).eval (n : ℝ) * ⌊(n : ℝ) / k⌋ ^ (i : ℕ))
  := by
  open Polynomial in
  classical
  let M : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k, (X - C (C (1/(k:ℝ)) * (Polynomial.X - C (j:ℝ))))
  have hm : M.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)
  have hd : M.natDegree = k := by
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    rw [Finset.sum_congr rfl (fun j _ => natDegree_X_sub_C _)]; simp
  refine ⟨fun i => -(M.coeff i), fun n => ?_⟩
  set f := ⌊(n:ℝ)/k⌋ with hf
  have kp : (0:ℝ) < k := by exact_mod_cast kpos
  have h1 := Int.floor_le ((n:ℝ)/k)
  have h2 := Int.lt_floor_add_one ((n:ℝ)/k)
  rw [le_div_iff₀ kp] at h1
  rw [div_lt_iff₀ kp] at h2
  have a : (0:ℤ) ≤ n - k*f := by
    have : ((k*f:ℤ):ℝ) ≤ n := by push_cast; linarith
    have := Int.cast_le.mp this; omega
  have b : n - k*f < k := by
    have : ((n:ℤ):ℝ) < ((k*f+k:ℤ):ℝ) := by push_cast; nlinarith
    have := Int.cast_lt.mp this; omega
  have h0 : (M.map (evalRingHom (n:ℝ))).eval (f:ℝ) = 0 := by
    simp only [M, Polynomial.map_prod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := (n - k * f).toNat)
    · rw [Finset.mem_range]; omega
    · have : (((n - k*f).toNat : ℕ):ℝ) = (n:ℝ) - k*f := by
        have hh : (((n - k*f).toNat : ℕ):ℤ) = n - k*f := Int.toNat_of_nonneg a
        exact_mod_cast hh
      simp [this]
      field_simp
      ring
  rw [eval_eq_sum_range' (n := k+1) (by rw [natDegree_map_of_leadingCoeff_ne_zero] <;> simp [hd, hm.leadingCoeff]), Finset.sum_range_succ] at h0
  have hl : (M.coeff k) = 1 := by rw [← hd]; exact hm
  simp only [coeff_map, coe_evalRingHom, hl] at h0
  simp at h0
  rw [← Finset.sum_coe_sort] at h0
  have : ((f:ℝ))^k = -∑ i : Finset.range k, (M.coeff i).eval (n:ℝ) * (f:ℝ)^(i:ℕ) := by linarith
  rw [this, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp
