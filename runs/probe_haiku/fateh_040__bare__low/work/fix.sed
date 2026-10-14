s|    haveI hspl : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits :=|    haveI hspl : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits :=|
s|      ⟨IsSplittingField.splits f.SplittingField f⟩|      ⟨SplittingField.splits f⟩\n    haveI hsplf : IsSplittingField ℚ f.SplittingField f :=\n      ⟨SplittingField.splits f, SplittingField.adjoin_rootSet f⟩|
s|    haveI : IsGalois ℚ f.SplittingField := IsGalois.of_separable_splitting_field hsep|    haveI : IsGalois ℚ f.SplittingField := IsGalois.of_separable_splitting_field hsep|
