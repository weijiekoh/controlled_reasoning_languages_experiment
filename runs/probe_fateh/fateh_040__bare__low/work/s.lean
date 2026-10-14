import Mathlib
open Polynomial
example (f:ℚ[X]) (K:Type)[Field K][Algebra ℚ K][IsSplittingField ℚ K f] [Fact (map (algebraMap ℚ K) f).Splits]: Function.Injective (Polynomial.Gal.restrict f K) := by
  exact?
