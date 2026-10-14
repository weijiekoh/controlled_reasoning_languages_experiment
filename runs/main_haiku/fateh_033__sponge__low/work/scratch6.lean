import Mathlib
open Polynomial
example (f : ℚ[X]) (hf' : Irreducible f) (a b : f.SplittingField) (ha' : a ∈ f.rootSet f.SplittingField) (g : f.Gal) : True := by
  have hsplit : Fact ((map (algebraMap ℚ f.SplittingField) f).Splits) := ⟨SplittingField.splits f⟩
  have k : (g • (⟨a, ha'⟩ : f.rootSet f.SplittingField) : f.SplittingField) = g a := by
    simp?
  trivial
#check @Polynomial.Gal.restrict_smul
#check @Polynomial.Gal.rootsEquivRoots
