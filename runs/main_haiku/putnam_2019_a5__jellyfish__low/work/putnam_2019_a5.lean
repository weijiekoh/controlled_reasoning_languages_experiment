import Mathlib

open Topology Filter

noncomputable abbrev putnam_2019_a5_solution : ℕ → ℕ := (fun p : ℕ => (p - 1) / 2)
/--
Let $p$ be an odd prime number, and let $\mathbb{F}_p$ denote the field of integers modulo $p$. Let $\mathbb{F}_p[x]$ be the ring of polynomials over $\mathbb{F}_p$, and let $q(x) \in \mathbb{F}_p[x]$ be given by $q(x)=\sum_{k=1}^{p-1} a_kx^k$, where $a_k=k^{(p-1)/2}\mod{p}$. Find the greatest nonnegative integer $n$ such that $(x-1)^n$ divides $q(x)$ in $\mathbb{F}_p[x]$.
-/
theorem putnam_2019_a5
  (p : ℕ)
  (q : Polynomial (ZMod p))
  (a : ℕ → ZMod p)
  (npoly : ℕ → Polynomial (ZMod p))
  (podd : Odd p)
  (pprime : p.Prime)
  (hq : ∀ k : ℕ, q.coeff k = a k)
  (ha0 : a 0 = 0 ∧ ∀ k > p - 1, a k = 0)
  (haother : ∀ k : Set.Icc 1 (p - 1), a k = ((k : ℕ) ^ ((p - 1) / 2)) % p)
  (hnpoly : ∀ n : ℕ, npoly n = (Polynomial.X - 1) ^ n) :
  IsGreatest {n | npoly n ∣ q} (putnam_2019_a5_solution p) :=
by
  haveI := Fact.mk pprime
  haveI : NeZero p := ⟨pprime.ne_zero⟩
  have hp2 := pprime.two_le
  obtain ⟨t, ht⟩ := podd
  have ht1 : 1 ≤ t := by omega
  have hsol : putnam_2019_a5_solution p = t := by
    unfold putnam_2019_a5_solution
    show (p - 1) / 2 = t
    omega
  rw [hsol]
  have hak : ∀ k < p, a k = (k : ZMod p) ^ t := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [ha0.1]
      simp [zero_pow (show t ≠ 0 by omega)]
    · have h := haother ⟨k, Set.mem_Icc.mpr ⟨hpos, by omega⟩⟩
      have h' : (p - 1) / 2 = t := by omega
      rw [h'] at h
      have h2 : a k = (((k ^ t) % p : ℕ) : ZMod p) := h
      rw [h2, ZMod.natCast_mod, Nat.cast_pow]
  have hsumZ : ∀ g : ℕ → ZMod p,
      ∑ n ∈ Finset.range p, g n = ∑ x : ZMod p, g x.val := by
    intro g
    apply Finset.sum_nbij' (fun n : ℕ => (n : ZMod p)) (fun x : ZMod p => x.val)
    · intro n _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro n hn
      rw [Finset.mem_range] at hn
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt hn]
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro n hn
      rw [Finset.mem_range] at hn
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt hn]
  have hPlow : ∀ e, e < p - 1 → ∑ n ∈ Finset.range p, (n : ZMod p) ^ e = 0 := by
    intro e he
    rw [hsumZ (fun n => (n : ZMod p) ^ e)]
    simp only [ZMod.natCast_zmod_val]
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) e (by rw [ZMod.card]; exact he)
  have hPtop : ∑ n ∈ Finset.range p, (n : ZMod p) ^ (p - 1) = -1 := by
    rw [hsumZ (fun n => (n : ZMod p) ^ (p - 1))]
    simp only [ZMod.natCast_zmod_val]
    have hx : ∀ x : ZMod p, x ^ (p - 1) = if x = 0 then 0 else 1 := by
      intro x
      split_ifs with h0
      · subst h0; simp [zero_pow (show p - 1 ≠ 0 by omega)]
      · exact ZMod.pow_card_sub_one_eq_one h0
    simp only [hx]
    rw [Finset.sum_ite]
    simp [Finset.filter_ne', ZMod.card]
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  have hmon : ∀ n, (descPochhammer (ZMod p) n).Monic := by
    intro n
    induction n with
    | zero => simp [descPochhammer_zero]
    | succ n ih =>
      rw [descPochhammer_succ_right]
      exact ih.mul (by simpa using Polynomial.monic_X_sub_C (n : ZMod p))
  have hevalQ : ∀ i k : ℕ, (descPochhammer (ZMod p) i).eval (k : ZMod p)
      = (i.factorial : ZMod p) * (k.choose i : ZMod p) := by
    intro i k
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  have hHasse : ∀ i, (Polynomial.hasseDeriv i q).eval 1
      = ∑ k ∈ Finset.range p, a k * (k.choose i : ZMod p) := by
    intro i
    have hdeg : (Polynomial.hasseDeriv i q).natDegree < p + i := by
      have : (Polynomial.hasseDeriv i q).natDegree ≤ p + i - 1 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [Polynomial.hasseDeriv_coeff, hq, ha0.2 (N + i) (by omega), mul_zero]
      omega
    rw [Polynomial.eval_eq_sum_range' hdeg]
    simp only [one_pow, mul_one, Polynomial.hasseDeriv_coeff, hq]
    set F : ℕ → ZMod p := fun k => a k * (k.choose i : ZMod p) with hFdef
    have hF0 : ∀ k < i, F k = 0 := by
      intro k hk
      simp [hFdef, Nat.choose_eq_zero_of_lt hk]
    have hshift : ∀ M, ∑ n ∈ Finset.range M, F (n + i) = ∑ k ∈ Finset.range (M + i), F k := by
      intro M
      induction M with
      | zero =>
        simp only [zero_add, Finset.sum_range_zero]
        exact (Finset.sum_eq_zero (fun k hk => hF0 k (Finset.mem_range.mp hk))).symm
      | succ M ih =>
        rw [Finset.sum_range_succ, ih, show M + 1 + i = (M + i) + 1 by omega,
          Finset.sum_range_succ]
    have hcongr : ∀ n, ((((n + i).choose i : ℕ) : ZMod p) * a (n + i)) = F (n + i) := by
      intro n; simp [hFdef, mul_comm]
    simp only [hcongr]
    rw [hshift (p + i), show p + i + i = p + (i + i) by omega, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range (i + i), F (p + x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp [hFdef, ha0.2 (p + x) (by omega)]
    rw [h0, add_zero]
  have hG : ∀ i, (i.factorial : ZMod p) * (Polynomial.hasseDeriv i q).eval 1
      = ∑ k ∈ Finset.range p, (k : ZMod p) ^ t * (descPochhammer (ZMod p) i).eval (k : ZMod p) := by
    intro i
    rw [hHasse, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hevalQ, hak k (Finset.mem_range.mp hk)]
    ring
  have hz : ∀ (c : ZMod p) (j : ℕ), j < t →
      ∑ k ∈ Finset.range p, (k : ZMod p) ^ t * (c * (k : ZMod p) ^ j) = 0 := by
    intro c j hj
    have : ∑ k ∈ Finset.range p, (k : ZMod p) ^ t * (c * (k : ZMod p) ^ j)
        = c * ∑ k ∈ Finset.range p, (k : ZMod p) ^ (t + j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros; ring
    rw [this, hPlow (t + j) (by omega), mul_zero]
  have hlow : ∀ i < t, ∑ k ∈ Finset.range p, (k : ZMod p) ^ t
      * (descPochhammer (ZMod p) i).eval (k : ZMod p) = 0 := by
    intro i hi
    simp only [Polynomial.eval_eq_sum_range, descPochhammer_natDegree]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz _ j (by rw [Finset.mem_range] at hj; omega)
  have htop : ∑ k ∈ Finset.range p, (k : ZMod p) ^ t
      * (descPochhammer (ZMod p) t).eval (k : ZMod p) = -1 := by
    simp only [Polynomial.eval_eq_sum_range, descPochhammer_natDegree]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun j hj => hz _ j (by rw [Finset.mem_range] at hj; exact hj)),
      zero_add]
    have hc : (descPochhammer (ZMod p) t).coeff t = 1 := by
      have := (hmon t).coeff_natDegree
      rw [descPochhammer_natDegree] at this
      exact this
    rw [hc]
    have : ∑ k ∈ Finset.range p, (k : ZMod p) ^ t * (1 * (k : ZMod p) ^ t)
        = ∑ n ∈ Finset.range p, (n : ZMod p) ^ (p - 1) := by
      apply Finset.sum_congr rfl
      intros; rw [one_mul, ← pow_add]; congr 1; omega
    rw [this, hPtop]
  have hdvd : ∀ n, (Polynomial.X - Polynomial.C (1 : ZMod p)) ^ n ∣ q
      ↔ ∀ i < n, (Polynomial.hasseDeriv i q).eval 1 = 0 := by
    intro n
    rw [Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply, Polynomial.X_pow_dvd_iff]
    simp only [Polynomial.taylor_coeff]
  have hX : ∀ n, npoly n = (Polynomial.X - Polynomial.C (1 : ZMod p)) ^ n := by
    intro n; rw [hnpoly, Polynomial.C_1]
  have hHt : (Polynomial.hasseDeriv t q).eval 1 ≠ 0 := by
    intro h
    have := hG t
    rw [h, mul_zero, htop] at this
    exact one_ne_zero (neg_eq_zero.mp this.symm)
  have hLow : ∀ i < t, (Polynomial.hasseDeriv i q).eval 1 = 0 := by
    intro i hi
    have h := hG i
    rw [hlow i hi] at h
    have hf : (i.factorial : ZMod p) ≠ 0 := by
      intro h0
      have := (ZMod.natCast_eq_zero_iff _ _).mp h0
      rw [pprime.dvd_factorial] at this
      omega
    exact (mul_eq_zero.mp h).resolve_left hf
  refine ⟨?_, ?_⟩
  · show npoly t ∣ q
    rw [hX, hdvd]
    intro i hi
    exact hLow i hi
  · intro n hn
    have hn' : npoly n ∣ q := hn
    by_contra hcon
    push_neg at hcon
    have h1 : npoly (t + 1) ∣ npoly n := by
      rw [hX, hX]
      exact pow_dvd_pow _ (by omega)
    have h2 : npoly (t + 1) ∣ q := dvd_trans h1 hn'
    rw [hX, hdvd] at h2
    exact hHt (h2 t (by omega))
