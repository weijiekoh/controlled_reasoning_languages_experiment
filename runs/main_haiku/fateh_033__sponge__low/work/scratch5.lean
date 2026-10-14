import Mathlib
open Polynomial
example (f : ℚ[X]) (hf' : Irreducible f) (a b : f.SplittingField) (ha' : a ∈ f.rootSet f.SplittingField) (hb' : b ∈ f.rootSet f.SplittingField) (g : f.Gal) : True := by
  have hsplit : Fact ((map (algebraMap ℚ f.SplittingField) f).Splits) := ⟨SplittingField.splits f⟩
  have : MulAction.IsPretransitive f.Gal (f.rootSet f.SplittingField) :=
    Polynomial.Gal.galAction_isPretransitive f _ hf'
  have k1 : g a = b ↔ g • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨b, hb'⟩ := by
    rw [Subtype.ext_iff, Gal.smul_def]
    sorry
  have k2 : g a = b ↔ g • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨b, hb'⟩ := by
    rw [Subtype.ext_iff]
    simp only [Gal.smul_def]
    sorry
  have k3 : g a = b ↔ g • (⟨a, ha'⟩ : f.rootSet f.SplittingField) = ⟨b, hb'⟩ := by
    rw [Subtype.ext_iff]
    rfl
  trivial
