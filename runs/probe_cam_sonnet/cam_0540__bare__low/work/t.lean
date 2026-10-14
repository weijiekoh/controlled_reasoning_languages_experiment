import Mathlib
example : sSup (∅ : Set (WithTop ℝ)) = 0 := by 
  rw [WithTop.sSup_eq (by simp) (by simp)]
  simp
