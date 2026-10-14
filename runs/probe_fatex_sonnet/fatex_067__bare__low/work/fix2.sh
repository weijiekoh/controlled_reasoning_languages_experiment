f=fatex_067.lean
perl -0pi -e 's/      rw \[h0\] at this\n      simpa \[c, MvPowerSeries.coeff_one\] using this/      rw [h0, show Λ 0 v = 0 by simp [Λ]] at this\n      simpa [c, MvPowerSeries.coeff_one] using this/' $f
perl -0pi -e 's/      simp \[Finsupp.single_eq_single_iff\]\n/      simp [Finsupp.single_eq_single_iff]\n      split_ifs <;> first | rfl | omega | (exfalso; omega)\n/' $f
perl -0pi -e 's/rw \[MvPowerSeries.algebraMap_apply\]; simp\)/rw [MvPowerSeries.algebraMap_apply]; simp [MvPowerSeries.constantCoeff_C])/' $f
perl -0pi -e 's/    exact not_finite ℕ \|>.elim \(Module.Finite.finite_of_linearIndependent hli\) /    have : Finite ℕ := Module.Finite.finite_of_linearIndependent hli\n    exact not_finite ℕ/' $f
