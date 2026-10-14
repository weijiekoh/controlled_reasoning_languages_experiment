import Mathlib

noncomputable abbrev brualdi_ch5_9_solution : ℕ → ℤ := fun n => (-9 : ℤ)^n

/--
Evaluate the sum $\sum_{k=0}^{n}(-1)^{k}\binom{n}{k} 10^{k}$.
-/
theorem brualdi_ch5_9 (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * 10 ^ k =
    brualdi_ch5_9_solution n := by sorry
