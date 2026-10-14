import Mathlib

open Real

example : ∃ g : ℕ → ℕ, (∀ n : ℕ, 0 < n → 0 < g n) ∧
    ∀ n : ℕ, 0 < n → ((g (g n) : ℝ) ^ ((1:ℝ)/4)) ≤ (g (n + 1) : ℝ) - (g n : ℝ) := by
  refine ⟨fun n => n ^ 2, fun n hn => by positivity, fun n hn => ?_⟩
  have h1 : ((n ^ 2) ^ 2 : ℕ) = n ^ 4 := by ring
  have h2 : (((n^2)^2 : ℕ) : ℝ) = (n:ℝ)^4 := by push_cast; ring
  simp only
  rw [h2]
  have h3 : ((n:ℝ)^4) ^ ((1:ℝ)/4) = (n:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [h3]
  push_cast
  have : (1:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith
