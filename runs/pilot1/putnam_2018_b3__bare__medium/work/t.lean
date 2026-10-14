import Mathlib

theorem key (a m : ℕ) (ha : 0 < a) : 2^a-1 ∣ 2^m-1 ↔ a ∣ m := by
  have h := Nat.pow_sub_one_gcd_pow_sub_one 2 a m
  constructor
  · intro d
    have : (2^a-1).gcd (2^m-1) = 2^a-1 := Nat.gcd_eq_left d
    rw [this] at h
    have h1 : 1 ≤ 2^a := Nat.one_le_two_pow
    have h2 : 1 ≤ 2^(a.gcd m) := Nat.one_le_two_pow
    have : 2^a = 2^(a.gcd m) := by omega
    have := Nat.pow_right_injective (le_refl 2) this
    rw [this]; exact Nat.gcd_dvd_right _ _
  · intro d
    rw [Nat.gcd_eq_left d] at h
    rw [← h]; exact Nat.gcd_dvd_right _ _

theorem X
  (n : ℕ) (hn : 0 < n) :
  (n < 10^100 ∧ ((n : ℤ) ∣ (2^n : ℤ) ∧ (n - 1 : ℤ) ∣ (2^n - 1 : ℤ) ∧ (n - 2 : ℤ) ∣ (2^n - 2 : ℤ))) ↔ n ∈ ({2^2, 2^4, 2^16, 2^256} : Set ℕ) := by
  constructor
  · rintro ⟨hlt, h1, h2, h3⟩
    have h1' : n ∣ 2^n := by exact_mod_cast h1
    obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1'
    have a0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at h2
      · exact h
    have h2' : 2^a - 1 ∣ 2^(2^a) - 1 := by
      have : ((2:ℕ)^a : ℤ) - 1 ∣ (2:ℤ)^(2^a) - 1 := by exact_mod_cast h2
      have h1 : 1 ≤ 2^a := Nat.one_le_two_pow
      have h4 : 1 ≤ 2^(2^a) := Nat.one_le_two_pow
      zify [h1, h4]
      exact_mod_cast this
    have := (key a _ a0).1 h2'
    obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
    have b0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · simp at h3
      · exact h
    have hb2 : 2 ≤ 2^b := by
      calc 2 = 2^1 := rfl
        _ ≤ 2^b := Nat.pow_le_pow_right (by norm_num) b0
    -- third
    have h3' : 2^(2^b-1) - 1 ∣ 2^(2^(2^b)-1) - 1 := by
      obtain ⟨k, hk⟩ := h3
      set A := 2^b with hA
      set N := 2^A with hN
      have hA1 : 2^A = 2 * 2^(A-1) := by
        rw [← pow_succ']; congr 1; omega
      have hN1 : 2^N = 2 * 2^(N-1) := by
        rw [← pow_succ']; congr 1
        have : 1 ≤ N := Nat.one_le_two_pow
        omega
      have p1 : 1 ≤ 2^(A-1) := Nat.one_le_two_pow
      have p2 : 1 ≤ 2^(N-1) := Nat.one_le_two_pow
      have e1 : ((2^A : ℕ) : ℤ) = 2 * 2^(A-1) := by exact_mod_cast hA1
      have e2 : ((2^N : ℕ) : ℤ) = 2 * 2^(N-1) := by exact_mod_cast hN1
      have e3 : (N:ℤ) = 2^A := by simp [hN]
      sorry
    sorry
  · rintro (rfl | rfl | rfl | rfl) <;> sorry
