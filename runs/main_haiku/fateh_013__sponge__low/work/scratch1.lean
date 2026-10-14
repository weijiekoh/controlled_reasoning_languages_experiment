import Mathlib
open Matrix
#check @IsPGroup.iff_card
#check @Subgroup.eq_of_le_of_card_ge
#check @Nat.card_eq_of_bijective
#check @ZMod.card_units
#check @Nat.card_zmod
#check @Subgroup.card_subgroup_dvd_card
#check @Subgroup.mem_normalizer_iff
#check @Units.inv_mul
example (p : ℕ) [Fact p.Prime] : Finite (GL (Fin 2) (ZMod p)) := inferInstance
example (p : ℕ) [Fact p.Prime] : Finite (Sylow p (GL (Fin 2) (ZMod p))) := inferInstance
