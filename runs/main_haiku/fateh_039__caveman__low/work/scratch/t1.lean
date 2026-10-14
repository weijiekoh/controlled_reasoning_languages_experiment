import Mathlib
open Polynomial
#check @FiniteField.card_rootsOfUnity
#check @FiniteField.pow_card_sub_one_eq_one
#check @IsCyclic.exists_ofOrder_eq_natCard
#check @card_rootSet_eq_natDegree
#check @separable_X_pow_sub_C
#check @SplittingField.adjoin_rootSet
#check @IsPrimitiveRoot.eq_pow_of_pow_eq_one
#check @Units.orderOf_coe
#check @IsPrimitiveRoot.iff_orderOf
#check @orderOf_pow_of_dvd
#check @FiniteField.isCyclic_units
#check @exists_root_of_splits
example : Finite (SplittingField (X^15 - C (2:ZMod 7))) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  infer_instance
