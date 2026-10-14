import Mathlib

/--
Prove that $D_{n}$ is an even number if and only if $n$ is an odd number.
-/
theorem brualdi_ch6_21 (n : ℕ) : Even (numDerangements n) ↔ Odd n := by
  have h : ∀ n, (Even (numDerangements n) ↔ Odd n) ∧ (Even (numDerangements (n+1)) ↔ Odd (n+1)) := by
    intro n
    induction n with
    | zero => simp [numDerangements]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [numDerangements_add_two, Nat.even_mul]
      have a := ih.1
      have b := ih.2
      simp only [Nat.odd_iff, Nat.even_iff, Nat.even_add_one, Nat.even_add] at *
      omega
  exact (h n).1
