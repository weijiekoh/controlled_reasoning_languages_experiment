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
  have hfloor : ∀ n : ℤ, ⌊(n:ℝ)/k⌋ = n / (k:ℤ) := by
    intro n
    rw [Int.floor_eq_iff]
    have hk' : (0:ℝ) < k := by exact_mod_cast kpos
    have h1 : n % (k:ℤ) = n - (k:ℤ) * (n / (k:ℤ)) := Int.emod_def n k
    have h2 := Int.emod_nonneg n (by omega : (k:ℤ) ≠ 0)
    have h3 := Int.emod_lt_of_pos n (by omega : (0:ℤ) < k)
    have h1s : (n:ℝ) = ((n % (k:ℤ) : ℤ):ℝ) + (k:ℝ) * ((n / (k:ℤ) : ℤ):ℝ) := by
      rw [h1]; push_cast; ring
    have h2' : (0:ℝ) ≤ ((n % (k:ℤ) : ℤ):ℝ) := by exact_mod_cast h2
    have h3' : ((n % (k:ℤ) : ℤ):ℝ) < (k:ℝ) := by exact_mod_cast h3
    constructor
    · rw [le_div_iff₀ hk']; nlinarith
    · rw [div_lt_iff₀ hk']; nlinarith
  -- G(n, Y) = ∏_j (n - j - k Y) as polynomial in Y with coefficients in ℝ[X]
  set f : ℕ → Polynomial (Polynomial ℝ) := fun j =>
    Polynomial.C (Polynomial.X - Polynomial.C (j:ℝ)) + Polynomial.C (Polynomial.C (-(k:ℝ))) * Polynomial.X with hf
  set G : Polynomial (Polynomial ℝ) := ∏ j ∈ Finset.range k, f j with hG
  have hfdeg : ∀ j, (f j).natDegree = 1 ∧ (f j).leadingCoeff = Polynomial.C (-(k:ℝ)) := by
    intro j
    have ha : Polynomial.C (-(k:ℝ)) ≠ 0 := by
      rw [Ne, Polynomial.C_eq_zero]; simp; omega
    have := Polynomial.natDegree_linear (R := Polynomial ℝ) ha (b := Polynomial.X - Polynomial.C (j:ℝ))
    have hl := Polynomial.leadingCoeff_linear (R := Polynomial ℝ) ha (b := Polynomial.X - Polynomial.C (j:ℝ))
    refine ⟨?_, ?_⟩
    · simpa [hf, add_comm] using this
    · simpa [hf, add_comm] using hl
  have hfne : ∀ j, f j ≠ 0 := by
    intro j h
    have := (hfdeg j).1
    rw [h] at this; simp at this
  have hGdeg : G.natDegree = k := by
    rw [hG, Polynomial.natDegree_prod _ _ (fun j _ => hfne j)]
    simp [(hfdeg _).1]
  have hGlc : G.coeff k = Polynomial.C ((-(k:ℝ))^k) := by
    have : G.coeff k = G.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hGdeg]
    rw [this, hG, Polynomial.leadingCoeff_prod]
    simp only [(hfdeg _).2]
    rw [Finset.prod_const, Finset.card_range, ← Polynomial.C_pow]
  have hc : (-(k:ℝ))^k ≠ 0 := by
    apply pow_ne_zero; have : (k:ℝ) ≠ 0 := by exact_mod_cast kpos.ne'
    exact neg_ne_zero.mpr this
  -- evaluation
  have hev : ∀ n : ℤ, ∀ x : ℝ, Polynomial.eval₂ (Polynomial.evalRingHom (n:ℝ)) x G
      = ∏ j ∈ Finset.range k, ((n:ℝ) - (j:ℝ) - (k:ℝ) * x) := by
    intro n x
    rw [← Polynomial.coe_eval₂RingHom, hG, map_prod]
    apply Finset.prod_congr rfl
    intro j _
    simp [hf]
    ring
  refine ⟨fun i => Polynomial.C (-(1 / (-(k:ℝ))^k)) * G.coeff (i:ℕ), ?_⟩
  intro n
  rw [hfloor n]
  set x : ℝ := ((n / (k:ℤ) : ℤ) : ℝ) with hx
  have hzero : Polynomial.eval₂ (Polynomial.evalRingHom (n:ℝ)) x G = 0 := by
    rw [hev]
    apply Finset.prod_eq_zero (i := (n % (k:ℤ)).toNat)
    · rw [Finset.mem_range]
      have h3 := Int.emod_lt_of_pos n (by omega : (0:ℤ) < k)
      have h2 := Int.emod_nonneg n (by omega : (k:ℤ) ≠ 0)
      omega
    · have h1 : n % (k:ℤ) = n - (k:ℤ) * (n / (k:ℤ)) := Int.emod_def n k
      have h2 := Int.emod_nonneg n (by omega : (k:ℤ) ≠ 0)
      have hc2 : (((n % (k:ℤ)).toNat : ℕ) : ℝ) = ((n % (k:ℤ) : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]
      rw [hc2, hx]
      have : ((n:ℤ):ℝ) = (((n % (k:ℤ)) + (k:ℤ) * (n / (k:ℤ)) : ℤ) : ℝ) := by
        congr 1; omega
      push_cast at this
      linarith
  rw [Polynomial.eval₂_eq_sum_range, hGdeg, Finset.sum_range_succ, hGlc] at hzero
  have key : ∑ i ∈ Finset.range k, (G.coeff i).eval (n:ℝ) * x^i = -((-(k:ℝ))^k) * x^k := by
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at hzero
    linarith
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (∑ i : Finset.range k, -(1 / (-(k:ℝ))^k) * Polynomial.eval (n:ℝ) (G.coeff (i:ℕ)) * x^(i:ℕ))
      = ∑ i ∈ Finset.range k, -(1 / (-(k:ℝ))^k) * Polynomial.eval (n:ℝ) (G.coeff i) * x^i
      from Finset.sum_coe_sort _ (fun i => -(1 / (-(k:ℝ))^k) * Polynomial.eval (n:ℝ) (G.coeff i) * x^i)]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, key]
  field_simp
