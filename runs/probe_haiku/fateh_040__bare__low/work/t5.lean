import Mathlib
open Polynomial
example (f : ℚ[X]) (σ : f.Gal) (x : f.SplittingField) (hx : x ∈ f.rootSet f.SplittingField) : True := by
  have hF : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits := ⟨SplittingField.splits f⟩
  have e1 := @Polynomial.Gal.galActionHom_restrict ℚ _ f f.SplittingField _ _ hF σ ⟨x, hx⟩
  trivial
example (f : ℚ[X]) (σ : f.Gal) (x : f.SplittingField) (hx : x ∈ f.rootSet f.SplittingField) : True := by
  have hF : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits := ⟨SplittingField.splits f⟩
  have e1 := Polynomial.Gal.galActionHom_restrict f f.SplittingField σ ⟨x, hx⟩
  trivial
