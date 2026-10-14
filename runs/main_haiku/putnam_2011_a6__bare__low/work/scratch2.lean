import Mathlib
#check @Multiplicative.ofMul
#check @Multiplicative.toAdd
#check @toAdd_ofMul
#check @Fintype.card_multiplicative
#check @ofMul_toAdd
example (G : Type) [CommGroup G] (x : G) : Multiplicative.toAdd (Multiplicative.ofMul x) = x := rfl
