import Mathlib

noncomputable abbrev putnam_2018_b3_solution : Set ℕ := {2^2, 2^4, 2^16, 2^256}
lemma D (a b : ℕ) (h : 2^a - 1 ∣ 2^b - 1) : a ∣ b := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 a b
  rw [Nat.gcd_eq_left h] at hg
  have p1 : 1 ≤ 2^a := Nat.one_le_two_pow
  have p2 : 1 ≤ 2^(a.gcd b) := Nat.one_le_two_pow
  have : 2^(a.gcd b) = 2^a := by omega
  have := Nat.pow_right_injective (le_refl 2) this
  exact (Nat.gcd_eq_left_iff_dvd.1 this.symm)

lemma E (a b : ℕ) (h : a ∣ b) : (2:ℤ)^a - 1 ∣ 2^b - 1 := by
  obtain ⟨c, rfl⟩ := h
  have := sub_dvd_pow_sub_pow ((2:ℤ)^a) 1 c
  simpa [← pow_mul] using this

lemma R (k : ℕ) (hk : 2 ≤ k) (h1 : k ∣ 2^k) (h2 : (k-1) ∣ 2^k - 1) :
    ((2^k:ℕ) : ℤ) ∣ (2^(2^k):ℤ) ∧ (((2^k:ℕ):ℤ) - 1 ∣ (2:ℤ)^(2^k) - 1) ∧
    (((2^k:ℕ):ℤ) - 2 ∣ (2:ℤ)^(2^k) - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
  have hN : 2^(m+1) = (2^(m+1) - 1) + 1 := by have : 1 ≤ 2^(m+1) := Nat.one_le_two_pow; omega
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    exact pow_dvd_pow _ (Nat.le_of_dvd (by positivity) h1)
  · push_cast
    exact E _ _ h1
  · push_cast
    have e1 : (2:ℤ)^(m+1) - 2 = 2 * (2^m - 1) := by ring
    have e2 : (2:ℤ)^(2^(m+1)) - 2 = 2 * (2^(2^(m+1) - 1) - 1) := by
      conv_lhs => rw [hN]
      ring
    rw [e1, e2]
    apply mul_dvd_mul_left
    apply E
    simpa using h2

theorem putnam_2018_b3
  (n : ℕ) (hn : 0 < n) :
  (n < 10^100 ∧ ((n : ℤ) ∣ (2^n : ℤ) ∧ (n - 1 : ℤ) ∣ (2^n - 1 : ℤ) ∧ (n - 2 : ℤ) ∣ (2^n - 2 : ℤ))) ↔ n ∈ putnam_2018_b3_solution := by
  constructor
  · rintro ⟨hlt, h1, h2, h3⟩
    have h1' : n ∣ 2^n := by exact_mod_cast h1
    obtain ⟨k, hkn, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1'
    have p1 : 1 ≤ 2^k := Nat.one_le_two_pow
    have p2 : 2 ≤ 2^(2^k) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) p1
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · norm_num at h2
      · norm_num at h3
    have h2' : 2^k - 1 ∣ 2^(2^k) - 1 := by
      have : ((2^k - 1 : ℕ):ℤ) ∣ ((2^(2^k) - 1 : ℕ):ℤ) := by
        rw [Nat.cast_sub p1, Nat.cast_sub (by omega)]; push_cast; exact_mod_cast h2
      exact_mod_cast this
    have hk1 := D _ _ h2'
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk1
    have hj1 : 2^j - 1 ∣ 2^(2^j) - 1 := by
      have : ((2^(2^j) - 2 : ℕ):ℤ) ∣ ((2^(2^(2^j)) - 2 : ℕ):ℤ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast
        have := h3; push_cast at this; exact this
      have hh : 2 * (2^(2^j-1) - 1) ∣ 2 * (2^(2^(2^j)-1) - 1) := by
        have q1 : 1 ≤ 2^j := Nat.one_le_two_pow
        have q2 : 1 ≤ 2^(2^j) := Nat.one_le_two_pow
        have e1 : 2^(2^j) - 2 = 2 * (2^(2^j-1) - 1) := by
          obtain ⟨t, ht⟩ : ∃ t, 2^j = t + 1 := ⟨2^j-1, by omega⟩
          rw [ht]; simp [pow_succ]; omega
        have e2 : 2^(2^(2^j)) - 2 = 2 * (2^(2^(2^j)-1) - 1) := by
          obtain ⟨t, ht⟩ : ∃ t, 2^(2^j) = t + 1 := ⟨2^(2^j)-1, by omega⟩
          rw [ht]; simp [pow_succ]; omega
        rw [← e1, ← e2]
        exact_mod_cast this
      have hh2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hh
      have := D _ _ hh2
      have q1 : 1 ≤ 2^j := Nat.one_le_two_pow
      have q2 : 1 ≤ 2^(2^j) := Nat.one_le_two_pow
      have := E (2^j - 1) (2^(2^j) - 1) this
      have h4 : ((2^j - 1 : ℕ):ℤ) ∣ ((2^(2^j) - 1 : ℕ):ℤ) := by
        rw [Nat.cast_sub q1, Nat.cast_sub q2]; push_cast; exact_mod_cast this
      sorry
    sorry
  · sorry
