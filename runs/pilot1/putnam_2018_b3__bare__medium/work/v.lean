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
      have hA1 : (2:ℤ)^(2^b) = 2 * 2^(2^b-1) := by
        rw [← pow_succ']; congr 1; omega
      have hN1 : (2:ℤ)^(2^(2^b)) = 2 * 2^(2^(2^b)-1) := by
        rw [← pow_succ']; congr 1
        have : 1 ≤ 2^(2^b) := Nat.one_le_two_pow
        omega
      push_cast at h3
      rw [hN1] at h3
      rw [hA1] at h3
      have h5 : (2:ℤ) * (2^(2^b-1) - 1) ∣ 2 * (2^(2^(2^b)-1) - 1) := by
        convert h3 using 1 <;> ring
      have h6 := (mul_dvd_mul_iff_left (by norm_num : (2:ℤ) ≠ 0)).1 h5
      have p1 : 1 ≤ 2^(2^b-1) := Nat.one_le_two_pow
      have p2 : 1 ≤ 2^(2^(2^b)-1) := Nat.one_le_two_pow
      zify [p1, p2]
      exact_mod_cast h6
    have h7 := (key (2^b-1) _ (by omega)).1 h3'
    have h9 : b ∣ 2^b := (key b _ b0).1 h7
    obtain ⟨c, hc, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h9
    have hc4 : c < 4 := by
      by_contra hcc
      have : 2^4 ≤ 2^c := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h16 : 2^(2^4) ≤ 2^(2^c) := Nat.pow_le_pow_right (by norm_num) this
      have h17 : 2^(2^(2^4)) ≤ 2^(2^(2^c)) := Nat.pow_le_pow_right (by norm_num) h16
      have h18 : 10^100 ≤ 2^333 := by rw [show (333:ℕ)=256+77 from rfl, pow_add]; norm_num
      have h19 : 2^333 ≤ 2^(2^(2^4)) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    interval_cases c <;> simp
  · intro hm
    have : ∃ b, 0 < b ∧ b ∣ 2^b ∧ n = 2^(2^b) ∧ b ≤ 8 := by
      rcases hm with rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨4, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨8, by norm_num, by norm_num, by norm_num, by norm_num⟩
    obtain ⟨b, b0, hbd, rfl, hb8⟩ := this
    have hb2 : 2 ≤ 2^b := by
      calc 2 = 2^1 := rfl
        _ ≤ 2^b := Nat.pow_le_pow_right (by norm_num) b0
    have hlt : 2^(2^b) < 10^100 := by
      have : 2^(2^b) ≤ 2^(2^8) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hb8)
      have h20 : 2^(2^8) < 10^100 := by norm_num
      omega
    refine ⟨hlt, ?_, ?_, ?_⟩
    · have : 2^(2^b) ∣ 2^(2^(2^b)) :=
        pow_dvd_pow 2 (Nat.lt_two_pow_self).le
      exact_mod_cast this
    · have h1 : 1 ≤ 2^(2^b) := Nat.one_le_two_pow
      have h4 : 1 ≤ 2^(2^(2^b)) := Nat.one_le_two_pow
      have hd : 2^b ∣ 2^(2^b) := pow_dvd_pow 2 (Nat.lt_two_pow_self).le
      have := (key (2^b) _ (by omega)).2 hd
      zify [h1, h4] at this
      exact_mod_cast this
    · have h7 : 2^b - 1 ∣ 2^(2^b) - 1 := (key b _ b0).2 hbd |> fun h => by
        sorry
    · have h7 : 2^b - 1 ∣ 2^(2^b) - 1 := by
        have := (key b (2^b) b0).2 hbd
        sorry
      sorry
