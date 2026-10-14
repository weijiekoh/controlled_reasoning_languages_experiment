f=fatex_067.lean
# line-based edits using perl
perl -0pi -e 's/    have := MvPowerSeries.coeff_add_monomial_mul.*?simpa using this\n/    show MvPowerSeries.coeff (Finsupp.single i0 (j+1)) (MvPowerSeries.X i0 * b) = MvPowerSeries.coeff (Finsupp.single i0 j) b\n    have e1 : Finsupp.single i0 (j+1) = Finsupp.single i0 1 + Finsupp.single i0 j := by\n      rw [← Finsupp.single_add, add_comm]\n    rw [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul]\n/s' $f
perl -0pi -e 's/    simpa \[c\] using MvPowerSeries.coeff_zero_X_mul b i0/    show MvPowerSeries.coeff (Finsupp.single i0 0) (MvPowerSeries.X i0 * b) = 0\n    rw [Finsupp.single_zero]\n    exact MvPowerSeries.coeff_zero_X_mul b i0/' $f
perl -0pi -e 's/      rw \[h0\] at this\n      simp at this\n/      rw [h0] at this\n/' $f
perl -0pi -e 's/have h1 : c \(j\+1\) 1 = 0 := by.*?\n/have h1 : c (j+1) 1 = 0 := by\n        show MvPowerSeries.coeff (Finsupp.single i0 (j+1)) 1 = 0\n        rw [MvPowerSeries.coeff_one]; simp [Finsupp.single_eq_zero]\n/' $f
perl -0pi -e 's/      simp only \[c, X0, MvPowerSeries.coeff_X_pow\]\n.*?\n      sorry\n/      show MvPowerSeries.coeff (Finsupp.single i0 i) (MvPowerSeries.X i0 ^ j) = _\n      rw [MvPowerSeries.coeff_X_pow]\n      simp [Finsupp.single_eq_single_iff]\n/s' $f
perl -0pi -e 's/\(fun r => by simp\)/(fun r => by rw [MvPowerSeries.algebraMap_apply]; simp)/' $f
perl -0pi -e 's/\(w⁻¹ : \(A ⊗\[k\] A\)ˣ\)/((w⁻¹ : (A ⊗[k] A)ˣ) : A ⊗[k] A)/g; s/exact w.mul_inv/exact_mod_cast w.mul_inv/' $f
perl -0pi -e 's/simp \[aug, X0\] at this/simp [aug, X0, MvPowerSeries.constantCoeff_X] at this/' $f
