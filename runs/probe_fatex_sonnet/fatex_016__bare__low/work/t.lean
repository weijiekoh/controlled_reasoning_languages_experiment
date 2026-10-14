import Mathlib
open IntermediateField
variable (F E : Type) [Field F] [Field E] [Algebra F E] (L : IntermediateField F E) (K : IntermediateField F L) (p : ℕ) (hp : p.Prime)
 [FiniteDimensional F K] [IsGalois F K] [IsGalois K L]
#synth IsScalarTower F K E
#synth Normal F K
#synth Algebra K E
#check @IsPGroup.iff_card
#check @Normal.minpoly_eq_iff_mem_orbit
#check @AlgEquiv.restrictNormal_commutes
#check @AlgEquiv.restrictNormalHom_surjective
