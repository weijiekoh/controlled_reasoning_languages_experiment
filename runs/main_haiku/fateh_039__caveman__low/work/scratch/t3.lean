import Mathlib
open Polynomial
#check @SplittingField.splits
#check @Polynomial.SplittingField.splits
#check @orderOf_units
#check @Units.orderOf_coe
#check @Subgroup.card_subgroup_dvd_card
#check @orderOf_dvd_natCard
#check @IsCyclic.exists_ofOrder_eq_natCard
#check @mem_rootsOfUnity
example : (X ^ 15 - 2 : (ZMod 7)[X]) = X ^ 15 - C 2 := by simp
example : True := by
  letI : Fact (Nat.Prime 7) := by decide
  have : Finite (X ^ 15 - 2 : (ZMod 7)[X]).SplittingField := inferInstance
  trivial
example : (3:ZMod 7)^3 = 6 := by decide
