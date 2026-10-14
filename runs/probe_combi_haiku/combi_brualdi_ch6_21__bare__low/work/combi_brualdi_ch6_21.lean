import Mathlib

/--
Prove that $D_{n}$ is an even number if and only if $n$ is an odd number.
-/
theorem brualdi_ch6_21 (n : ℕ) : Even (numDerangements n) ↔ Odd n := by
  have key : ∀ m, numDerangements m % 2 = (m + 1) % 2 ∧
      numDerangements (m + 1) % 2 = (m + 2) % 2 := by
    intro m
    induction m with
    | zero => simp [numDerangements_zero, numDerangements_one]
    | succ k ih =>
      refine ⟨ih.2.trans (by omega), ?_⟩
      rw [show k + 1 + 1 = k + 2 from rfl, numDerangements_add_two, Nat.mul_mod,
        Nat.add_mod (numDerangements k), ih.1, ih.2]
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · have h1 : (k + 1) % 2 = 1 := by omega
        have h2 : (k + 2) % 2 = 0 := by omega
        have h3 : (k + 1 + 2) % 2 = 1 := by omega
        rw [h1, h2, h3]
      · have h1 : (k + 1) % 2 = 0 := by omega
        have h3 : (k + 1 + 2) % 2 = 0 := by omega
        rw [h1, h3]
        simp
  rw [Nat.even_iff, Nat.odd_iff]
  have := (key n).1
  omega
