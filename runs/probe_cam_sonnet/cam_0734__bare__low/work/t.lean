import Mathlib
open scoped Matrix.Norms.L2Operator
example (r : Fin 2 → ℝ) : ‖r‖ = ⨆ i, ‖r i‖₊ := by exact?
example (r : Fin 2 → ℝ) : ‖r‖ = max |r 0| |r 1| := by
  simp [Pi.norm_def, Fin.sup_univ_eq_iSup]
