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
: ∃ n : ℕ, {b : ℕ | b ≥ 1 ∧ (Nat.digits b n).length = 3 ∧ List.Palindrome (Nat.digits b n)}.ncard ≥ 2002 :=
by
  have key : ∀ F : ℕ, (∀ j, 1 ≤ j → j ≤ 2002 → ∃ m, 1 ≤ m ∧ F = j*m) →
      ∃ n : ℕ, {b : ℕ | b ≥ 1 ∧ (Nat.digits b n).length = 3 ∧ List.Palindrome (Nat.digits b n)}.ncard ≥ 2002 := by
    intro F hF
    obtain ⟨N, hN⟩ : ∃ N, N = F*2003^3 := ⟨_, rfl⟩
    refine ⟨N^2, ?_⟩
    have hq : ∀ j, 1 ≤ j → j ≤ 2002 → ∃ q, 8036054027 ≤ q ∧ N = j*q ∧ N/j = q := by
      intro j hj1 hj2
      obtain ⟨m, hm1, hm⟩ := hF j hj1 hj2
      have h3 : (8036054027:ℕ) ≤ m*2003^3 := by nlinarith
      refine ⟨m*2003^3, h3, ?_, ?_⟩
      · rw [hN, hm]; ring
      · have e : N = j*(m*2003^3) := by rw [hN, hm]; ring
        rw [e]; exact Nat.mul_div_cancel_left _ (by omega)
    have mem : ∀ j, 1 ≤ j → j ≤ 2002 → N/j - 1 ∈ {b : ℕ | b ≥ 1 ∧ (Nat.digits b (N^2)).length = 3 ∧ List.Palindrome (Nat.digits b (N^2))} := by
      intro j hj1 hj2
      obtain ⟨q, hq8, hqe, hqd⟩ := hq j hj1 hj2
      rw [hqd]
      obtain ⟨b, rfl⟩ : ∃ b, q = b+1 := ⟨q-1, by omega⟩
      have hn : N^2 = j^2 + b*(2*j^2 + b*j^2) := by rw [hqe]; ring
      rw [hn, Nat.add_sub_cancel]
      obtain ⟨a, ha⟩ : ∃ a, a = j^2 := ⟨_, rfl⟩
      rw [← ha]
      have ha0 : a ≠ 0 := by rw [ha]; positivity
      have ha8 : a ≤ 4008004 := by rw [ha]; nlinarith
      have hab : a < b := by omega
      have h2 : 2*a < b := by omega
      have hbb : 1 < b := by omega
      have hdig : Nat.digits b (a + b*(2*a + b*a)) = [a, 2*a, a] := by
        rw [Nat.digits_add b hbb a (2*a + b*a) hab (Or.inl ha0),
          Nat.digits_add b hbb (2*a) a h2 (Or.inl (by omega)),
          Nat.digits_of_lt b a ha0 hab]
      simp only [Set.mem_setOf_eq]
      rw [hdig]
      refine ⟨by omega, by simp, ?_⟩
      exact List.Palindrome.of_reverse_eq rfl
    have hTsub : {b : ℕ | b ≥ 1 ∧ (Nat.digits b (N^2)).length = 3 ∧ List.Palindrome (Nat.digits b (N^2))} ⊆ Set.Iic (N^2) := by
      rintro b ⟨hb1, hlen, -⟩
      simp only [Set.mem_Iic]
      have hn0 : N^2 ≠ 0 := by
        intro h; rw [h] at hlen; simp at hlen
      rcases Nat.lt_or_ge b 2 with hb | hb
      · have : b = 1 := by omega
        subst this
        exact Nat.pos_of_ne_zero hn0
      · rw [Nat.digits_len b (N^2) (by omega) hn0] at hlen
        have hl : Nat.log b (N^2) = 2 := by omega
        have hp := Nat.pow_log_le_self b hn0
        rw [hl] at hp
        nlinarith
    have hinj : Set.InjOn (fun j => N/j - 1) (Finset.Icc 1 2002 : Set ℕ) := by
      intro j hj k hk h
      have hj' := Finset.mem_Icc.mp (Finset.mem_coe.mp hj)
      have hk' := Finset.mem_Icc.mp (Finset.mem_coe.mp hk)
      obtain ⟨qj, hqj8, hqje, hqjd⟩ := hq j hj'.1 hj'.2
      obtain ⟨qk, hqk8, hqke, hqkd⟩ := hq k hk'.1 hk'.2
      have h' : N/j - 1 = N/k - 1 := h
      rw [hqjd, hqkd] at h'
      have hqq : qj = qk := by omega
      have e : j*qj = k*qj := by rw [← hqje, hqke, hqq]
      exact Nat.eq_of_mul_eq_mul_right (by omega) e
    have himg : ((fun j => N/j - 1) '' (Finset.Icc 1 2002 : Set ℕ)).ncard = 2002 := by
      rw [Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset]; simp
    have hsub : (fun j => N/j - 1) '' (Finset.Icc 1 2002 : Set ℕ) ⊆ {b : ℕ | b ≥ 1 ∧ (Nat.digits b (N^2)).length = 3 ∧ List.Palindrome (Nat.digits b (N^2))} := by
      rintro _ ⟨j, hj, rfl⟩
      have hj' := Finset.mem_Icc.mp (Finset.mem_coe.mp hj)
      exact mem j hj'.1 hj'.2
    rw [ge_iff_le, ← himg]
    exact Set.ncard_le_ncard hsub ((Set.finite_Iic _).subset hTsub)
  exact key (Nat.factorial 2002) (fun j hj1 hj2 => by
    obtain ⟨m, hm⟩ := Nat.dvd_factorial (by omega) hj2
    refine ⟨m, ?_, hm⟩
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      exact absurd hm (Nat.factorial_ne_zero 2002)
    · exact h)
