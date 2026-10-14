import Mathlib

open Nat Set Topology Filter

/--
A palindrome in base $b$ is a positive integer whose base-$b$
digits read the same backwards and forwards; for example,
$2002$ is a 4-digit palindrome in base 10. Note that 200 is not
a palindrome in base 10, but it is the 3-digit palindrome
242 in base 9, and 404 in base 7. Prove that there is an integer
which is a 3-digit palindrome in base $b$ for at least 2002
different values of $b$.
-/
theorem putnam_2002_b5
: ∃ n : ℕ, {b : ℕ | b ≥ 1 ∧ (Nat.digits b n).length = 3 ∧ List.Palindrome (Nat.digits b n)}.ncard ≥ 2002 := by
  have main : ∀ K : ℕ, ∃ n : ℕ, K ≤ {b : ℕ | b ≥ 1 ∧ (Nat.digits b n).length = 3 ∧ List.Palindrome (Nat.digits b n)}.ncard := by
    intro K
    set M := K ! * (2*K^3+2*K+2) with hM
    have hf : 1 ≤ K ! := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K)
    have hM0 : 0 < M := by
      rw [hM]; have : 0 < 2*K^3+2*K+2 := by omega
      exact Nat.mul_pos (Nat.factorial_pos K) this
    have hdvd : ∀ k, 1 ≤ k → k ≤ K → k ∣ M := fun k h1 h2 =>
      Dvd.dvd.mul_right (Nat.dvd_factorial h1 h2) _
    have hq : ∀ k, 1 ≤ k → k ≤ K → k * (M/k) = M := fun k h1 h2 =>
      Nat.mul_div_cancel' (hdvd k h1 h2)
    have hlow : ∀ k, 1 ≤ k → k ≤ K → 2*k^2+2 < M/k := by
      intro k h1 h2
      have h3 := hq k h1 h2
      have hk3 : k^3 ≤ K^3 := Nat.pow_le_pow_left h2 3
      have hk1 : k^2 = k*k := by ring
      have h4 : k*(2*k^2+2) ≤ 2*K^3+2*K := by
        have : k*(2*k^2+2) = 2*k^3+2*k := by ring
        omega
      have h5 : 2*K^3+2*K+2 ≤ M := by
        rw [hM]; nlinarith
      have : k*(2*k^2+2) < k*(M/k) := by rw [h3]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨M^2, ?_⟩
    let f : ℕ → ℕ := fun k => M / k - 1
    have hkey : ∀ k, 1 ≤ k → k ≤ K →
        f k ∈ {b : ℕ | b ≥ 1 ∧ (Nat.digits b (M^2)).length = 3 ∧ List.Palindrome (Nat.digits b (M^2))} := by
      intro k h1 h2
      have hl := hlow k h1 h2
      have h3 := hq k h1 h2
      obtain ⟨b, hb⟩ : ∃ b, M/k = b+1 := ⟨M/k-1, by omega⟩
      have hfb : f k = b := by simp only [f]; omega
      rw [hfb]
      have hMe : M = k*(b+1) := by rw [← hb]; exact h3.symm
      have hn : M^2 = k^2 + b*(2*k^2 + b*k^2) := by
        rw [hMe]; ring
      have hk0 : k^2 ≠ 0 := by positivity
      have hbk : k^2 < b := by omega
      have h2b : 2*k^2 < b := by omega
      have hb1 : 1 < b := by omega
      have h2k0 : 2*k^2 ≠ 0 := by positivity
      have hd : Nat.digits b (M^2) = [k^2, 2*k^2, k^2] := by
        rw [hn, Nat.digits_add b hb1 (k^2) (2*k^2 + b*k^2) hbk (Or.inl hk0),
          Nat.digits_add b hb1 (2*k^2) (k^2) h2b (Or.inl h2k0),
          Nat.digits_of_lt b (k^2) hk0 hbk]
      refine ⟨by omega, ?_, ?_⟩
      · rw [hd]; rfl
      · rw [hd]; exact List.Palindrome.of_reverse_eq rfl
    have hinj : Set.InjOn f (Set.Icc 1 K) := by
      intro j hj k hk hjk
      have hj' := Set.mem_Icc.mp hj
      have hk' := Set.mem_Icc.mp hk
      have hlj := hlow j hj'.1 hj'.2
      have hlk := hlow k hk'.1 hk'.2
      have he : M/j = M/k := by simp only [f] at hjk; omega
      have e1 := hq j hj'.1 hj'.2
      have e2 := hq k hk'.1 hk'.2
      rw [he] at e1
      exact Nat.eq_of_mul_eq_mul_right (by omega) (e1.trans e2.symm)
    have hsub : f '' Set.Icc 1 K ⊆
        {b : ℕ | b ≥ 1 ∧ (Nat.digits b (M^2)).length = 3 ∧ List.Palindrome (Nat.digits b (M^2))} := by
      rintro _ ⟨k, hk, rfl⟩
      exact hkey k (Set.mem_Icc.mp hk).1 (Set.mem_Icc.mp hk).2
    have hfin : {b : ℕ | b ≥ 1 ∧ (Nat.digits b (M^2)).length = 3 ∧ List.Palindrome (Nat.digits b (M^2))}.Finite := by
      apply (Set.finite_Iic (M^2)).subset
      rintro b ⟨hb1, hlen, _⟩
      simp only [Set.mem_Iic]
      by_contra hc
      push_neg at hc
      have hne : M^2 ≠ 0 := by positivity
      rw [Nat.digits_of_lt b (M^2) hne hc] at hlen
      simp at hlen
    have hcard : (Set.Icc 1 K).ncard = K := by
      rw [← Finset.coe_Icc, Set.ncard_coe_finset]; simp
    calc K = (Set.Icc 1 K).ncard := hcard.symm
      _ = (f '' Set.Icc 1 K).ncard := (Set.ncard_image_of_injOn hinj).symm
      _ ≤ _ := Set.ncard_le_ncard hsub hfin
  exact main 2002
