import Mathlib
open Polynomial IntermediateField

theorem f_irred : Irreducible (X ^ 4 - X ^ 2 - 1 : ℚ[X]) := sorry

instance : IsSplittingField ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField (X ^ 4 - X ^ 2 - 1 : ℚ[X]) := Polynomial.IsSplittingField.splittingField _

theorem step1 : Nat.card (IntermediateField ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField)
   = Nat.card (Subgroup ((X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField ≃ₐ[ℚ] (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField)) := by
  have : IsGalois ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField :=
    IsGalois.of_separable_splitting_field f_irred.separable
  exact Nat.card_congr (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField)).toEquiv
