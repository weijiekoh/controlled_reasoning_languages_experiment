import Mathlib
open Polynomial
#check @Subgroup.card_mul_index
#check @MulAction.index_stabilizer
#check @MulAction.exists_smul_eq
#check @Polynomial.Gal.smul_def
#check @Equiv.subtypeEquiv
example (f : ℚ[X]) (g : f.Gal) (x : f.rootSet f.SplittingField) : ((g • x : f.rootSet f.SplittingField) : f.SplittingField) = g (x : f.SplittingField) := rfl
