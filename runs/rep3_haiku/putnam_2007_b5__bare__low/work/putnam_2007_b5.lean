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
  let f : ℕ → Polynomial (Polynomial ℝ) := fun r =>
    Polynomial.C (Polynomial.C (k:ℝ)) * Polynomial.X + Polynomial.C (Polynomial.C (r:ℝ) - Polynomial.X)
  let g : Polynomial (Polynomial ℝ) := ∏ r ∈ Finset.range k, f r
  have hk : (k:ℝ) ≠ 0 := by exact_mod_cast kpos.ne'
  have hlin : ∀ r, (f r).natDegree = 1 := fun r =>
    Polynomial.natDegree_linear (by simp; omega)
  have hlc : ∀ r, (f r).leadingCoeff = Polynomial.C (k:ℝ) := fun r => by
    rw [Polynomial.leadingCoeff, hlin r]
    simp [f]
  have hne : ∀ r ∈ Finset.range k, f r ≠ 0 := by
    intro r _ h
    have := hlin r
    rw [h] at this
    simp at this
  have hgdeg : g.natDegree = k := by
    simp only [g]
    rw [Polynomial.natDegree_prod _ _ hne]
    simp [hlin]
  have hglc : g.coeff k = Polynomial.C ((k:ℝ)^k) := by
    rw [show g.coeff k = g.leadingCoeff from by rw [Polynomial.leadingCoeff, hgdeg]]
    simp only [g]
    rw [Polynomial.leadingCoeff_prod]
    simp [hlc, map_pow]
  let ψ : Polynomial (Polynomial ℝ) →+* Polynomial ℝ := Polynomial.mapRingHom (Polynomial.evalRingHom (0:ℝ))
  refine ⟨fun i => Polynomial.C (-(1/(k:ℝ)^k)) * g.coeff (i:ℕ), ?_⟩
  intro n
  have hkpos : (0:ℝ) < k := by exact_mod_cast kpos
  set m : ℤ := ⌊(n:ℝ)/k⌋ with hm
  have hA : (m:ℝ) ≤ n/k := Int.floor_le _
  have hB : (n:ℝ)/k < m+1 := Int.lt_floor_add_one _
  have hA' : (m:ℝ)*k ≤ n := by rwa [le_div_iff₀ hkpos] at hA
  have hB' : (n:ℝ) < (m+1)*k := by rwa [div_lt_iff₀ hkpos] at hB
  have hA'' : (k:ℤ)*m ≤ n := by
    have : ((k:ℤ)*m : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  have hB'' : n < ((k:ℤ)*m) + k := by
    have : (n:ℝ) < ((k:ℤ)*m : ℝ) + k := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r:ℤ) = n - k*m := ⟨(n - k*m).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hrk : r ∈ Finset.range k := by
    rw [Finset.mem_range]
    have : (r:ℤ) < k := by rw [hr]; linarith
    exact_mod_cast this
  have h3 : (k:ℝ) * (m:ℝ) + (r:ℝ) = n := by
    have : ((r:ℤ):ℝ) = ((n - k*m : ℤ):ℝ) := by rw [hr]
    push_cast at this
    linarith
  have hg2 : Polynomial.map (Polynomial.evalRingHom (n:ℝ)) g
      = ∏ r ∈ Finset.range k, (Polynomial.C (k:ℝ) * Polynomial.X + Polynomial.C ((r:ℝ) - n)) := by
    simp [g, f, Polynomial.map_prod]
  have hzero : Polynomial.eval (m:ℝ) (∏ r ∈ Finset.range k, (Polynomial.C (k:ℝ) * Polynomial.X + Polynomial.C ((r:ℝ) - n))) = 0 := by
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hrk (by simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]; linarith)
  rw [← hg2] at hzero
  have hdeg : (Polynomial.map (Polynomial.evalRingHom (n:ℝ)) g).natDegree < k+1 := by
    have := Polynomial.natDegree_map_le (p := g) (f := Polynomial.evalRingHom (n:ℝ))
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_range_succ] at hzero
  have hcoef : ∀ i, (Polynomial.map (Polynomial.evalRingHom (n:ℝ)) g).coeff i = (g.coeff i).eval (n:ℝ) := fun i => by
    simp [Polynomial.coeff_map]
  simp only [hcoef] at hzero
  rw [hglc] at hzero
  simp only [Polynomial.eval_C] at hzero
  rw [Finset.sum_coe_sort (Finset.range k) (fun i => Polynomial.eval (n:ℝ) (Polynomial.C (-(1/(k:ℝ)^k)) * g.coeff i) * (m:ℝ)^i)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, ← Finset.mul_sum]
  have hS : ∑ i ∈ Finset.range k, (g.coeff i).eval (n:ℝ) * (m:ℝ)^i = -((k:ℝ)^k * (m:ℝ)^k) := by
    linarith
  rw [hS]
  field_simp
