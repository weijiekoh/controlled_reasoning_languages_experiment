import Mathlib
open Polynomial
#check @Polynomial.Gal.galActionHom_injective
#check @Polynomial.Gal.galAction_isPretransitive
#check @Polynomial.Splits.image_rootSet
#check @AlgEquiv.restrictNormal
#check @IsGalois.intermediateFieldEquivSubgroup
#check @Polynomial.Gal.galActionHom
#check @Rat.isSquare_natCast_iff
#check @Polynomial.Monic.irreducible_iff_natDegree
#check @MulAction.card_orbit_mul_card_stabilizer_eq_card_group
example : IsGalois ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField := inferInstance
