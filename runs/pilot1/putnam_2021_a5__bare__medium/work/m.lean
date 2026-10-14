theorem putnam_2021_a5
  (j : ℕ)
  (A : Finset ℕ)
  (S : ℕ → ℕ)
  (hA : A = {n | 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1})
  (hS : ∀ j' : ℕ, S j' = ∑ n ∈ A, n ^ j') :
  (2021 ∣ S j) ↔ j ∈ putnam_2021_a5_solution := by
  have hm : ∀ n, n ∈ A ↔ 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1 := fun n => by
    have := Set.ext_iff.1 hA n
    simpa using this
  have c43 : ((1932 : ℕ) : ZMod 43) ≠ 0 := by decide
  have c47 : ((1932 : ℕ) : ZMod 47) ≠ 0 := by decide
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  have k43 := key 43 (by norm_num) 3 (by norm_num) o43 c43 A hm j
  have k47 := key 47 (by norm_num) 5 (by norm_num) o47 c47 A hm j
  rw [hS]
  simp only [putnam_2021_a5_solution, Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 : 43 ∣ ∑ n ∈ A, n ^ j := dvd_trans ⟨47, by norm_num⟩ h
    have h2 : 47 ∣ ∑ n ∈ A, n ^ j := dvd_trans ⟨43, by norm_num⟩ h
    exact ⟨by simpa using k43.1 h1, by simpa using k47.1 h2⟩
  · rintro ⟨h1, h2⟩
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 43 47)
      (k43.2 (by simpa using h1)) (k47.2 (by simpa using h2))
    simpa using this
