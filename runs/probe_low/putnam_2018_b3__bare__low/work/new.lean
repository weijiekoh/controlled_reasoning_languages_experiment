import Mathlib

noncomputable abbrev putnam_2018_b3_solution : Set ℕ := {2^2, 2^4, 2^16, 2^256}
lemma D (a b : ℕ) (h : 2^a - 1 ∣ 2^b - 1) : a ∣ b := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 a b
  rw [Nat.gcd_eq_left h] at hg
  have p1 : 1 ≤ 2^a := Nat.one_le_two_pow
  have p2 : 1 ≤ 2^(a.gcd b) := Nat.one_le_two_pow
  have : 2^(a.gcd b) = 2^a := by omega
  have := Nat.pow_right_injective (le_refl 2) this
  exact (Nat.gcd_eq_left_iff_dvd.1 this)

lemma E (a b : ℕ) (h : a ∣ b) : (2:ℤ)^a - 1 ∣ 2^b - 1 := by
  obtain ⟨c, rfl⟩ := h
  have := sub_dvd_pow_sub_pow ((2:ℤ)^a) 1 c
  simpa [← pow_mul] using this

lemma N (a b c : ℕ) (ha : c ≤ a) (hb : c ≤ b) (h : (a:ℤ) - c ∣ (b:ℤ) - c) : a - c ∣ b - c := by
  have : ((a - c : ℕ):ℤ) ∣ ((b - c : ℕ):ℤ) := by
    rw [Nat.cast_sub ha, Nat.cast_sub hb]; exact h
  exact_mod_cast this

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
    have h2' : 2^k - 1 ∣ 2^(2^k) - 1 := N _ _ 1 p1 (by omega) (by exact_mod_cast h2)
    have hk1 := D _ _ h2'
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk1
    have q1 : 1 ≤ 2^j := Nat.one_le_two_pow
    have q2 : 1 ≤ 2^(2^j) := Nat.one_le_two_pow
    have h3' : 2^(2^j) - 2 ∣ 2^(2^(2^j)) - 2 := N _ _ 2 (by omega) (by omega) (by exact_mod_cast h3)
    have e1 : 2^(2^j) - 2 = 2 * (2^(2^j-1) - 1) := by
      obtain ⟨t, ht⟩ : ∃ t, 2^j = t + 1 := ⟨2^j-1, by omega⟩
      rw [ht]; simp [pow_succ]; omega
    have e2 : 2^(2^(2^j)) - 2 = 2 * (2^(2^(2^j)-1) - 1) := by
      obtain ⟨t, ht⟩ : ∃ t, 2^(2^j) = t + 1 := ⟨2^(2^j)-1, by omega⟩
      rw [ht]; simp [pow_succ]; omega
    rw [e1, e2] at h3'
    have hh2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3'
    have hj1 := D _ _ hh2
    have hj2 := D _ _ hj1
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hj2
    have hi4 : i < 4 := by
      by_contra hc
      push_neg at hc
      have a1 : 16 ≤ 2^i := by
        calc 16 = 2^4 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hc
      have a2 : 2^16 ≤ 2^(2^i) := Nat.pow_le_pow_right (by norm_num) a1
      have a3 : 2^(2^16) ≤ 2^(2^(2^i)) := Nat.pow_le_pow_right (by norm_num) a2
      have a4 : 10^100 < 2^(2^16) := by
        calc 10^100 < 2^400 := by norm_num
          _ ≤ 2^(2^16) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      have a5 : 2^(2^(2^i)) ≤ 2^(2^(2^i)) := le_refl _
      omega
    interval_cases i <;> simp [putnam_2018_b3_solution]
  · intro h
    simp only [putnam_2018_b3_solution, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    have key : ∀ k, 2 ≤ k → k ∣ 2^k → (k-1) ∣ 2^k - 1 → 2^k < 10^100 →
        (2^k < 10^100 ∧ (((2^k:ℕ):ℤ) ∣ (2^(2^k):ℤ) ∧ (((2^k:ℕ):ℤ) - 1 ∣ (2:ℤ)^(2^k) - 1) ∧
        (((2^k:ℕ):ℤ) - 2 ∣ (2:ℤ)^(2^k) - 2))) := fun k a b c d => ⟨d, R k a b c⟩
    rcases h with h | h | h | h <;> subst h
    · exact key 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact key 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact key 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact key 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
