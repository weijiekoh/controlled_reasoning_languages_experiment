import Mathlib
example : ∀ p q r x : Fin 3, p ≠ q → q ≠ r → p ≠ r → x ≠ p → x + p = q + r → False := by
  intro p q r x; revert p q r x; set_option synthInstance.maxSize 2000 in decide
