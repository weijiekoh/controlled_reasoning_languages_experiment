import Mathlib
open Polynomial
example (f : ℚ[X]) [Fact (map (algebraMap ℚ (SplittingField f)) f).Splits] (g : f.Gal) : True := by
  have : Normal ℚ (SplittingField f) := SplittingField.instNormal f
  have h2 : Gal.restrict f (SplittingField f) g = g := by
    apply AlgEquiv.ext
    intro z
    have hc := AlgEquiv.restrictNormal_commutes (g : SplittingField f ≃ₐ[ℚ] SplittingField f) (SplittingField f) z
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at hc
    simp only [Gal.restrict, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply]
    convert hc using 3
  trivial
