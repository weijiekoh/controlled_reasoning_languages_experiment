import Mathlib
open Module
#check @LinearIndependent.finite
#check @Module.Finite.finite_of_linearIndependent
#check @LinearIndependent.finite_of_isNoetherian
example {k : Type} [Field k] (r:k) (n:ℕ): MvPowerSeries.constantCoeff (MvPowerSeries.C r : MvPowerSeries (Fin n) k) = r := by
  simp [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_C]
