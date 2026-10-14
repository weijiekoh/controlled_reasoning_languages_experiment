import Mathlib
open Matrix
example (q : ℕ) [Fact (q+2).Prime] : Nat.card (GL (Fin 2) (ZMod (q+2))) = (q+2)*((q+1)*(q+1)*(q+3)) := by
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two, ZMod.card, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [show (q+2)^2 - 1 = (q+1)*(q+3) from Nat.sub_eq_of_eq_add (by ring),
      show (q+2)^2 - (q+2) = (q+2)*(q+1) from Nat.sub_eq_of_eq_add (by ring)]
  ring
example (q : ℕ) [Fact (q+2).Prime] : Fintype.card (ZMod (q+2))ˣ = (q+1) := by
  rw [ZMod.card_units]; rfl
#check @Nat.card_units
#check @Nat.card_eq_of_bijective
#check @Matrix.inv_eq_right_inv
#check @Subgroup.mem_normalizer_iff
#check @Matrix.coe_units_inv
#check @Matrix.isUnit_iff_isUnit_det
