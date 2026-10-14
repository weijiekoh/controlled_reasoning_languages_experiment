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
  have hkR : (0:ℝ) < k := by exact_mod_cast kpos
  have hk : (k:ℝ) ≠ 0 := hkR.ne'
  have hneg : (-(k:ℝ)) ≠ 0 := neg_ne_zero.mpr hk
  set c : ℝ := (-(k:ℝ))^k with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ hneg
  have hlin : ∀ a b : ℝ, a ≠ 0 →
      (Polynomial.C a * Polynomial.X + Polynomial.C b).leadingCoeff = a ∧
      (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 := by
    intro a b ha
    have hab : a * (b / a) = b := by field_simp
    have : Polynomial.C a * Polynomial.X + Polynomial.C b
        = Polynomial.C a * (Polynomial.X + Polynomial.C (b / a)) := by
      rw [mul_add, ← Polynomial.C_mul, hab]
    rw [this]
    constructor
    · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        Polynomial.leadingCoeff_X_add_C, mul_one]
    · rw [Polynomial.natDegree_C_mul ha, Polynomial.natDegree_X_add_C]
  have hne : ∀ a b : ℝ, a ≠ 0 → Polynomial.C a * Polynomial.X + Polynomial.C b ≠ 0 := by
    intro a b ha h
    have := (hlin a b ha).1
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact ha this.symm
  let F : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k,
    (Polynomial.C (Polynomial.C (-(k:ℝ))) * Polynomial.X
      + Polynomial.C (Polynomial.X - Polynomial.C (j:ℝ)))
  have hG : ∀ n : ℤ, F.map (Polynomial.evalRingHom (n:ℝ)) =
      ∏ j ∈ Finset.range k, (Polynomial.C (-(k:ℝ)) * Polynomial.X + Polynomial.C ((n:ℝ) - j)) := by
    intro n
    simp only [F, Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp [Polynomial.map_add, Polynomial.map_mul]
  refine ⟨fun i => Polynomial.C (-(1/c)) * F.coeff (i:ℕ), ?_⟩
  intro n
  have h1 : ((⌊(n:ℝ)/k⌋ : ℤ):ℝ) ≤ (n:ℝ)/k := Int.floor_le _
  have h2 : (n:ℝ)/k < ((⌊(n:ℝ)/k⌋ : ℤ):ℝ) + 1 := Int.lt_floor_add_one _
  generalize hm : ⌊(n:ℝ)/k⌋ = m at h1 h2 ⊢
  have h1' : (k:ℝ) * m ≤ n := by
    have := (le_div_iff₀ hkR).mp h1; linarith
  have h2' : (n:ℝ) < k * m + k := by
    have := (div_lt_iff₀ hkR).mp h2; nlinarith
  have hI1 : (k:ℤ) * m ≤ n := by exact_mod_cast h1'
  have hI2 : (n:ℤ) < k * m + k := by exact_mod_cast h2'
  obtain ⟨j0, hj0eq⟩ : ∃ j0 : ℕ, (j0:ℤ) = n - k * m :=
    ⟨(n - k * m).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hj0 : j0 < k := by
    have : (j0:ℤ) < k := by linarith
    exact_mod_cast this
  have hjR : ((j0:ℕ):ℝ) = (n:ℝ) - (k:ℝ) * (m:ℝ) := by
    have h := congrArg (fun z : ℤ => (z:ℝ)) hj0eq
    push_cast at h
    linarith
  have hev : (F.map (Polynomial.evalRingHom (n:ℝ))).eval (m:ℝ) = 0 := by
    rw [hG n, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hj0)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    linarith [hjR]
  have hlc : (∏ j ∈ Finset.range k,
      (Polynomial.C (-(k:ℝ)) * Polynomial.X + Polynomial.C ((n:ℝ) - j))).leadingCoeff = c := by
    rw [Polynomial.leadingCoeff_prod]
    rw [Finset.prod_congr rfl (fun j _ => (hlin (-(k:ℝ)) _ hneg).1), Finset.prod_const,
      Finset.card_range]
  have hdeg : (∏ j ∈ Finset.range k,
      (Polynomial.C (-(k:ℝ)) * Polynomial.X + Polynomial.C ((n:ℝ) - j))).natDegree = k := by
    rw [Polynomial.natDegree_prod _ _ (fun j _ => hne _ _ hneg)]
    rw [Finset.sum_congr rfl (fun j _ => (hlin (-(k:ℝ)) _ hneg).2), Finset.sum_const,
      Finset.card_range]
    simp
  have hck : (F.map (Polynomial.evalRingHom (n:ℝ))).coeff k = c := by
    rw [hG n]
    have := hlc
    unfold Polynomial.leadingCoeff at this
    rwa [hdeg] at this
  have hsum := Polynomial.eval_eq_sum_range' (n := k+1)
    (by rw [hG n, hdeg]; omega) (m:ℝ) (p := F.map (Polynomial.evalRingHom (n:ℝ)))
  rw [Finset.sum_range_succ, hck, hev] at hsum
  have hcoef : ∀ i : ℕ, (F.coeff i).eval (n:ℝ) = (F.map (Polynomial.evalRingHom (n:ℝ))).coeff i := by
    intro i
    rw [Polynomial.coeff_map]
    rfl
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  refine Eq.trans ?_ (Finset.sum_coe_sort (Finset.range k) (fun i => -(1/c) * Polynomial.eval (n:ℝ) (F.coeff i) * (m:ℝ)^i)).symm
  simp only [hcoef]
  have hmul : ∑ i ∈ Finset.range k, (-(1/c) * (F.map (Polynomial.evalRingHom (n:ℝ))).coeff i) * (m:ℝ)^i
      = -(1/c) * ∑ i ∈ Finset.range k, (F.map (Polynomial.evalRingHom (n:ℝ))).coeff i * (m:ℝ)^i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hmul]
  have hS : ∑ i ∈ Finset.range k, (F.map (Polynomial.evalRingHom (n:ℝ))).coeff i * (m:ℝ)^i
      = -(c * (m:ℝ)^k) := by linarith
  rw [hS]
  field_simp
