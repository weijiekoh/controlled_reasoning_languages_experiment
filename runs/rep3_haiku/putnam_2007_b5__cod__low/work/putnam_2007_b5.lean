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
  set c : ℝ := (-(k:ℝ))^k with hc
  have hk0 : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let f : ℕ → Polynomial (Polynomial ℝ) := fun j =>
    Polynomial.C (Polynomial.C (-(k:ℝ))) * Polynomial.X + Polynomial.C (Polynomial.X - Polynomial.C (j:ℝ))
  have hf : ∀ j, (f j).natDegree = 1 ∧ (f j).leadingCoeff = Polynomial.C (-(k:ℝ)) := by
    intro j
    have ha : (Polynomial.C (-(k:ℝ)) : Polynomial ℝ) ≠ 0 := by
      simpa using hk0
    have hd := Polynomial.natDegree_linear (a := Polynomial.C (-(k:ℝ))) (b := Polynomial.X - Polynomial.C (j:ℝ)) ha
    refine ⟨hd, ?_⟩
    unfold Polynomial.leadingCoeff
    rw [hd]
    simp [f]
  have hne : ∀ j, f j ≠ 0 := fun j h => by
    have := (hf j).1
    rw [h] at this
    simp at this
  set T := ∏ j ∈ Finset.range k, f j with hTdef
  have hT_deg : T.natDegree = k := by
    rw [hTdef, Polynomial.natDegree_prod _ _ (fun j _ => hne j)]
    rw [Finset.sum_congr rfl (fun j _ => (hf j).1)]
    simp
  have hT_lc : T.leadingCoeff = Polynomial.C c := by
    rw [hTdef, Polynomial.leadingCoeff_prod]
    rw [Finset.prod_congr rfl (fun j _ => (hf j).2), Finset.prod_const, Finset.card_range, ← map_pow]
  have hTk : T.coeff k = Polynomial.C c := by
    have := hT_lc
    unfold Polynomial.leadingCoeff at this
    rwa [hT_deg] at this
  have hc0 : c ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hk0)
  refine ⟨fun i => Polynomial.C (-c⁻¹) * T.coeff i, fun n => ?_⟩
  set m : ℤ := n / (k:ℤ) with hm
  have hkz : (k:ℤ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hr0 : 0 ≤ n % (k:ℤ) := Int.emod_nonneg _ hkz
  have hrk : n % (k:ℤ) < k := Int.emod_lt_of_pos _ (by omega)
  have hdiv : (k:ℤ) * m + n % (k:ℤ) = n := Int.mul_ediv_add_emod n k
  have hkpos : (0:ℝ) < k := by exact_mod_cast kpos
  have hfl : ⌊(n:ℝ)/k⌋ = m := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hkpos]
      have : (m:ℤ) * k ≤ n := by linarith
      exact_mod_cast (by linarith [this] : (m:ℤ) * k ≤ n)
    · rw [div_lt_iff₀ hkpos]
      have : n < (m+1) * k := by linarith
      have h' : (n:ℝ) < ((m:ℝ)+1) * k := by exact_mod_cast this
      linarith
  rw [hfl]
  set j := (n % (k:ℤ)).toNat with hj
  have hjk : j < k := by omega
  have hjr : (j:ℝ) = ((n % (k:ℤ) : ℤ):ℝ) := by
    have : (j:ℤ) = n % k := Int.toNat_of_nonneg hr0
    exact_mod_cast this
  have hreal : (k:ℝ) * (m:ℝ) + ((n % (k:ℤ) : ℤ):ℝ) = (n:ℝ) := by exact_mod_cast hdiv
  set Q : Polynomial ℝ := T.map (Polynomial.evalRingHom (n:ℝ)) with hQdef
  have hQ0 : Q.eval (m:ℝ) = 0 := by
    rw [hQdef, hTdef, Polynomial.map_prod, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.2 hjk)
    simp [f]
    rw [hjr]
    linarith
  have hsum : Q.eval (m:ℝ) = ∑ i ∈ Finset.range (k+1), (T.coeff i).eval (n:ℝ) * (m:ℝ)^i := by
    rw [Polynomial.eval_eq_sum_range' (n := k+1) (lt_of_le_of_lt Polynomial.natDegree_map_le (by omega))]
    simp [Polynomial.coeff_map]
  rw [Finset.sum_range_succ, hTk] at hsum
  simp only [Polynomial.eval_C] at hsum
  have hS : ∑ i ∈ Finset.range k, (T.coeff i).eval (n:ℝ) * (m:ℝ)^i = -(c * (m:ℝ)^k) := by
    linarith
  simp only [Finset.sum_coe_sort (Finset.range k) (fun i => (Polynomial.C (-c⁻¹) * T.coeff i).eval (n:ℝ) * (m:ℝ)^i)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have h2 : ∑ i ∈ Finset.range k, -c⁻¹ * (T.coeff i).eval (n:ℝ) * (m:ℝ)^i
      = -c⁻¹ * ∑ i ∈ Finset.range k, (T.coeff i).eval (n:ℝ) * (m:ℝ)^i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h2, hS]
  push_cast
  field_simp
