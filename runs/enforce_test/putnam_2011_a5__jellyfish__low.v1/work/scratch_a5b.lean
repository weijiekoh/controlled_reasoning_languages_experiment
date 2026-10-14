import Mathlib
example : ∃ i j : Fin 3, i ≠ j := ⟨0, 1, by decide⟩
#check @Real.sInf_nonneg
