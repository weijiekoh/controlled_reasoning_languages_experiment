import Mathlib
open Polynomial
#check @Polynomial.aeval_algHom_apply
#check @IntermediateField.mem_map
#check @Polynomial.mem_rootSet
example (f : ℚ[X]) : IsGalois ℚ f.SplittingField := by
  have : Fact (Irreducible f) := sorry
  exact inferInstance
