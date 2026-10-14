import Mathlib
#check @Additive.ofMul
#check @Additive.toMul
#check @Fintype.card_additive
#check @ofMul_prod
example (G : Type) [CommGroup G] : AddCommGroup (Additive G) := inferInstance
example (G : Type) [CommGroup G] [Fintype G] : Fintype (Additive G) := inferInstance
example (G : Type) [CommGroup G] (x : G) : (0 : Additive G) = Additive.ofMul 1 := rfl
example (G : Type) [CommGroup G] (x y : G) : Additive.ofMul (x*y) = Additive.ofMul x + Additive.ofMul y := rfl
