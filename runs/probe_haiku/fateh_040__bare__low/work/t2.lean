import Mathlib
set_option maxRecDepth 100000 in
theorem key5 : ∀ p : Equiv.Perm (Fin 5), ∀ x y z : Fin 5, x ≠ y → y ≠ z → x ≠ z → p x = x → p y = y → p z = z → p ≠ 1 → ∃ u v : Fin 5, u ≠ v ∧ p = Equiv.swap u v := by decide
