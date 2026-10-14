import Mathlib

open Real

example : (1/4 : ℝ) ∈ {r : ℝ | ∃ g : ℕ → ℕ, (∀ n : ℕ, 0 < n → 0 < g n) ∧
        ∀ n : ℕ, 0 < n → ((g (g n) : ℝ) ^ r) ≤ (g (n + 1) : ℝ) - (g n : ℝ)} := by
  refine ⟨fun n => n ^ 2, fun n hn => by positivity, fun n hn => ?_⟩
  simp only [Nat.cast_pow]
  have hn' : (0:ℝ) ≤ n := by positivity
  have h4 : (((n:ℝ) ^ 2) ^ 2) = ((n:ℝ)) ^ (4:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn']; norm_num
  rw [h4, ← Real.rpow_mul hn']
  norm_num
  nlinarith [sq_nonneg ((n:ℝ) - 1)]
