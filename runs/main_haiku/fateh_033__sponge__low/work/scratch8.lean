import Mathlib
open Polynomial
example (f : ℚ[X]) (g : f.Gal) : True := by
  have hsplit : Fact ((map (algebraMap ℚ f.SplittingField) f).Splits) :=
    ⟨by exact SplittingField.splits f⟩
  have hr : Gal.restrict f f.SplittingField g = g := by
    apply AlgEquiv.ext
    intro x
    simp only [Gal.restrict, AlgEquiv.restrictNormalHom_apply]
    have := AlgEquiv.restrictNormal_commutes g f.SplittingField x
    simpa using this
  trivial
