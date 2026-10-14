f=fatex_067.lean
perl -0pi -e 's/rw \[h0, show Λ 0 v = 0 by simp \[Λ\]\] at this\n      simpa \[c, MvPowerSeries.coeff_one\] using this/have hc01 : c 0 1 = 1 := by\n        show MvPowerSeries.coeff (Finsupp.single i0 0) 1 = 1\n        rw [Finsupp.single_zero, MvPowerSeries.coeff_one]; simp\n      rw [h0, show Λ 0 v = 0 by simp [Λ], hc01, one_smul] at this\n      simpa using this/' $f
perl -0pi -e 's/simp \[MvPowerSeries.constantCoeff_C\]\)/simp)/; s/Module.Finite.finite_of_linearIndependent hli/hli.finite/' $f
