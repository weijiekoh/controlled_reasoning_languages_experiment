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
  open Polynomial in
  have lin_lc : ∀ (a b : ℝ), a ≠ 0 → (C a * X + C b : ℝ[X]).leadingCoeff = a := by
    intro a b ha
    rw [leadingCoeff, natDegree_linear ha]; simp
  have lin_nd : ∀ (a b : ℝ), a ≠ 0 → (C a * X + C b : ℝ[X]).natDegree = 1 :=
    fun a b ha => natDegree_linear ha
  open Polynomial in
  have hk : (k:ℝ) ≠ 0 := by positivity
  -- the polynomial in Y with coefficients in ℝ[X]
  obtain ⟨F, hF⟩ : ∃ F : Polynomial (Polynomial ℝ),
      F = ∏ j ∈ Finset.range k, (C (C (k:ℝ)) * X + C (C (j:ℝ) - X)) := ⟨_, rfl⟩
  have hG : ∀ x : ℝ, F.map (Polynomial.evalRingHom x)
      = ∏ j ∈ Finset.range k, (C (k:ℝ) * X + C ((j:ℝ) - x)) := by
    intro x
    subst hF
    simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    simp
  have hGdeg : ∀ x : ℝ, (F.map (Polynomial.evalRingHom x)).natDegree ≤ k := by
    intro x
    rw [hG x]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.range k, 1 := Finset.sum_le_sum (fun j _ => by compute_degree!)
      _ = k := by simp
  have hGlead : ∀ x : ℝ, (F.map (Polynomial.evalRingHom x)).coeff k = (k:ℝ)^k := by
    intro x
    rw [hG x]
    have hnz : ∀ j : ℕ, (C (k:ℝ) * X + C ((j:ℝ) - x) : ℝ[X]) ≠ 0 := fun j h => by
      have := lin_nd (k:ℝ) ((j:ℝ) - x) hk
      rw [h] at this; simp at this
    have hdeg : (∏ j ∈ Finset.range k, (C (k:ℝ) * X + C ((j:ℝ) - x)) : ℝ[X]).natDegree = k := by
      rw [natDegree_prod _ _ (fun j _ => hnz j), Finset.sum_congr rfl (fun j _ => lin_nd _ _ hk)]
      simp
    have hlc : (∏ j ∈ Finset.range k, (C (k:ℝ) * X + C ((j:ℝ) - x)) : ℝ[X]).leadingCoeff = (k:ℝ)^k := by
      rw [leadingCoeff_prod, Finset.prod_congr rfl (fun j _ => lin_lc _ _ hk)]
      simp
    have h : (∏ j ∈ Finset.range k, (C (k:ℝ) * X + C ((j:ℝ) - x)) : ℝ[X]).leadingCoeff = (∏ j ∈ Finset.range k, (C (k:ℝ) * X + C ((j:ℝ) - x)) : ℝ[X]).coeff (∏ j ∈ Finset.range k, (C (k:ℝ) * X + C ((j:ℝ) - x)) : ℝ[X]).natDegree := rfl
    rw [hdeg, hlc] at h
    exact h.symm
  refine ⟨fun i => Polynomial.C (-(1/(k:ℝ)^k)) * F.coeff (i:ℕ), ?_⟩
  intro n
  set x : ℝ := (n:ℝ) with hx
  set m : ℤ := ⌊x / k⌋ with hm
  have h1 : (m:ℝ) * k ≤ x := by
    have := Int.floor_le (x / k)
    rw [← hm] at this
    have := (le_div_iff₀ (by positivity : (0:ℝ) < k)).1 this
    linarith
  have h2 : x < ((m:ℝ) + 1) * k := by
    have := Int.lt_floor_add_one (x / k)
    rw [← hm] at this
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < k)).1 this
    linarith
  have hr0 : (0:ℤ) ≤ n - k * m := by
    have : (m:ℝ) * k ≤ (n:ℝ) := h1
    have : (m * k : ℤ) ≤ n := by exact_mod_cast this
    linarith
  have hrk : n - k * m < (k:ℤ) := by
    have : (n:ℝ) < ((m:ℝ) + 1) * k := h2
    have : n < (m + 1) * k := by exact_mod_cast this
    linarith
  set j : ℕ := (n - k * m).toNat with hj
  have hjk : j < k := by omega
  have hjcast : ((j:ℕ):ℝ) = x - (k:ℝ) * m := by
    have : ((j:ℕ):ℤ) = n - k * m := Int.toNat_of_nonneg hr0
    have : ((j:ℕ):ℝ) = ((n - k * m : ℤ):ℝ) := by exact_mod_cast this
    rw [this]; push_cast; rw [hx]
  -- the root
  have hroot : (F.map (Polynomial.evalRingHom x)).eval (m:ℝ) = 0 := by
    rw [hG x, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.2 hjk)
    simp only [eval_add, eval_mul, eval_C, eval_X]
    rw [hjcast]; ring
  have hsum : (F.map (Polynomial.evalRingHom x)).eval (m:ℝ)
      = ∑ i ∈ Finset.range (k+1), (F.map (Polynomial.evalRingHom x)).coeff i * (m:ℝ)^i :=
    Polynomial.eval_eq_sum_range' (by have := hGdeg x; omega) _
  rw [Finset.sum_range_succ, hGlead x, hroot] at hsum
  have hfin : ∑ i : Finset.range k, (Polynomial.C (-(1/(k:ℝ)^k)) * F.coeff (i:ℕ)).eval x * (m:ℝ)^(i:ℕ)
      = -(1/(k:ℝ)^k) * ∑ i ∈ Finset.range k, (F.map (Polynomial.evalRingHom x)).coeff i * (m:ℝ)^i := by
    rw [Finset.sum_coe_sort (Finset.range k) (fun i => (Polynomial.C (-(1/(k:ℝ)^k)) * F.coeff i).eval x * (m:ℝ)^i)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.coeff_map]
    rw [show (Polynomial.evalRingHom x) (F.coeff i) = Polynomial.eval x (F.coeff i) from rfl]
    ring
  rw [hfin]
  have hmk : ((⌊(n:ℝ) / k⌋ : ℤ) : ℝ)^k = ((m:ℤ):ℝ)^k := rfl
  rw [hmk]
  have hkk : (k:ℝ)^k ≠ 0 := pow_ne_zero _ hk
  field_simp
  linarith
