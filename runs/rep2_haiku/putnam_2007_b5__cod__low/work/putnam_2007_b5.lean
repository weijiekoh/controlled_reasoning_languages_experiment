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
  have hk : (0:ℝ) < k := by exact_mod_cast kpos
  let a : ℕ → Polynomial ℝ := fun j => Polynomial.C (1/(k:ℝ)) * (Polynomial.X - Polynomial.C (j:ℝ))
  let G : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k, (Polynomial.X - Polynomial.C (a j))
  have hGm : G.Monic := Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
  have hGd : G.natDegree = k := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
    simp
  have hG1 : G ≠ 1 := by
    intro h
    rw [h] at hGd
    simp at hGd <;> omega
  set R := (Polynomial.X ^ k : Polynomial (Polynomial ℝ)) %ₘ G with hRdef
  have hR : R.natDegree < k := hGd ▸ Polynomial.natDegree_modByMonic_lt _ hGm hG1
  have hdiv := Polynomial.modByMonic_add_div (Polynomial.X ^ k) G
  refine ⟨fun i => R.coeff i, ?_⟩
  intro n
  set m := ⌊(n:ℝ)/k⌋ with hm
  have h1 : (m:ℝ) ≤ (n:ℝ)/k := Int.floor_le _
  have h2 : (n:ℝ)/k < m + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hk] at h1
  rw [div_lt_iff₀ hk] at h2
  have h1' : m * (k:ℤ) ≤ n := by exact_mod_cast h1
  have h2' : n < m * (k:ℤ) + k := by
    have : (n:ℝ) < m * k + k := by linarith
    exact_mod_cast this
  set j := (n - m * (k:ℤ)).toNat with hjdef
  have hj : (j:ℤ) = n - m * k := Int.toNat_of_nonneg (by linarith)
  have hjk : j < k := by
    have : (j:ℤ) < k := by linarith
    exact_mod_cast this
  have hG0 : Polynomial.eval₂ (Polynomial.evalRingHom (n:ℝ)) (m:ℝ) G = 0 := by
    simp only [G, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, a, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hjk)
    have hz : (n:ℤ) - (j:ℤ) = m * (k:ℤ) := by linarith
    have hzR : (n:ℝ) - (j:ℝ) = (m:ℝ) * (k:ℝ) := by exact_mod_cast hz
    rw [hzR, show (1/(k:ℝ)) * ((m:ℝ) * k) = m by field_simp, sub_self]
  have hkey := congrArg (Polynomial.eval₂ (Polynomial.evalRingHom (n:ℝ)) (m:ℝ)) hdiv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hkey
  rw [hG0, zero_mul, add_zero, ← hRdef, Polynomial.eval₂_eq_sum_range' _ hR] at hkey
  rw [← hkey]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_coe_sort (Finset.range k) (fun i => Polynomial.eval (n:ℝ) (R.coeff i) * (m:ℝ)^i)).symm
  simp [Polynomial.coe_evalRingHom]
