import Mathlib
open Polynomial
example (f : ℚ[X]) (σ : f.Gal) (x : f.SplittingField) (hx : x ∈ f.rootSet f.SplittingField) : True := by
  haveI hspl : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits := ⟨SplittingField.splits f⟩
  have e1 := Polynomial.Gal.galActionHom_restrict f f.SplittingField σ ⟨x, hx⟩
  trivial
example (f : ℚ[X]) (σ : f.Gal) (x : f.SplittingField) (hx : x ∈ f.rootSet f.SplittingField) : True := by
  haveI : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits := ⟨SplittingField.splits f⟩
  have e1 := Polynomial.Gal.galActionHom_restrict f f.SplittingField σ ⟨x, hx⟩
  trivial
