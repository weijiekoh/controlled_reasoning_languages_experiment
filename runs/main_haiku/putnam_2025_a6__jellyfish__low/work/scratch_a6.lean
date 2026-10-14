import Mathlib
def b : ℕ → ℤ
| 0 => 0
| n + 1 => 2 * (b n) ^ 2 + b n + 1
example : b 4 - 2 * b 2 = 2768 := by decide
example : b 3 = 37 := by decide
example : (2768:ℤ) % 16 = 0 ∧ (2768:ℤ) % 32 ≠ 0 := by decide
example : (2^6 : ℤ) ∣ b 8 - 2 * b 4 := by decide
example : ¬ ((2^7 : ℤ) ∣ b 8 - 2 * b 4) := by decide
