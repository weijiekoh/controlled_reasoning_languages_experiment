import Mathlib
open Matrix
example (q : ℕ) [Fact (q+2).Prime] : ∀ (a a' d d' b : ZMod (q+2)), a * a' = 1 → d * d' = 1 →
    (!![a, b; 0, d] * !![a', -(b * a' * d'); 0, d'] = 1 ∧
          !![a', -(b * a' * d'); 0, d'] * !![a, b; 0, d] = 1) := by
  intro a a' d d' b hA hD
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · exact hA
    · linear_combination (-(b*d'))*hA
    · exact hD
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hA
    · linear_combination (-(b*a'))*hD
    · linear_combination hD
