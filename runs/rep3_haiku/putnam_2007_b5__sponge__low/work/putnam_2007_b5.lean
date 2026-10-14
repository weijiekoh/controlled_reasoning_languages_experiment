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
  have hk : (0:ℝ) < k := by exact_mod_cast kpos
  let A : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k,
    (Polynomial.X - Polynomial.C (Polynomial.C (1/(k:ℝ)) * (Polynomial.X - Polynomial.C (j:ℝ))))
  have hmon : A.Monic := Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
  have hdeg : A.natDegree = k := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hcoeffk : A.coeff k = 1 := by
    rw [← hdeg]; exact hmon.coeff_natDegree
  refine ⟨fun i => -(A.coeff (i:ℕ)), ?_⟩
  intro n
  have h1 : ((⌊(n:ℝ)/k⌋ : ℤ):ℝ) ≤ (n:ℝ)/k := Int.floor_le _
  have h2 : (n:ℝ)/k < ((⌊(n:ℝ)/k⌋ : ℤ):ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hk] at h1
  rw [div_lt_iff₀ hk] at h2
  set m : ℤ := ⌊(n:ℝ)/k⌋ with hm
  have h1' : (k:ℤ)*m ≤ n := by
    have : ((k:ℤ)*m : ℝ) ≤ (n:ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h2' : n < (k:ℤ)*m + k := by
    have : (n:ℝ) < ((k:ℤ)*m + k : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hr0 : 0 ≤ n - (k:ℤ)*m := by linarith
  have hrk : n - (k:ℤ)*m < k := by linarith
  have hj : (n - (k:ℤ)*m).toNat < k := by omega
  have hjr : (((n - (k:ℤ)*m).toNat : ℕ) : ℤ) = n - (k:ℤ)*m := Int.toNat_of_nonneg hr0
  have hjR : (((n - (k:ℤ)*m).toNat : ℕ) : ℝ) = (n:ℝ) - (k:ℝ)*(m:ℝ) := by
    have := congrArg (fun z : ℤ => (z:ℝ)) hjr
    push_cast at this
    linarith
  have key : (Polynomial.eval₂RingHom (Polynomial.evalRingHom (n:ℝ)) (m:ℝ)) A = 0 := by
    simp only [A, map_prod]
    apply Finset.prod_eq_zero (i := (n - (k:ℤ)*m).toNat) (Finset.mem_range.mpr hj)
    simp only [Polynomial.coe_eval₂RingHom, map_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
    rw [hjR]
    field_simp
    ring
  have hψ : (A.map (Polynomial.evalRingHom (n:ℝ))).eval (m:ℝ) = 0 := by
    rw [Polynomial.eval_map]; exact key
  have hexp := Polynomial.eval_eq_sum_range' (p := A.map (Polynomial.evalRingHom (n:ℝ))) (n := k+1)
    (lt_of_le_of_lt Polynomial.natDegree_map_le (by rw [hdeg]; omega)) (m:ℝ)
  rw [Finset.sum_range_succ] at hexp
  have hsum : ∑ i : Finset.range k, (-(A.coeff (i:ℕ))).eval (n:ℝ) * (m:ℝ)^(i:ℕ)
      = ∑ i ∈ Finset.range k, (-(A.coeff i)).eval (n:ℝ) * (m:ℝ)^i :=
    Finset.sum_coe_sort (Finset.range k) (fun i => (-(A.coeff i)).eval (n:ℝ) * (m:ℝ)^i)
  rw [hsum]
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom, hcoeffk, map_one, Polynomial.eval_neg,
    neg_mul, Finset.sum_neg_distrib] at hexp hψ ⊢
  linarith
