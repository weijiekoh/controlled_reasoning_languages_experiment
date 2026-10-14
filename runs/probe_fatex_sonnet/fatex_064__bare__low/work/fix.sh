f=t7.lean
sed -i 's/      simp \[X_pow_eq_monomial, X, monomial_mul\]/      rw [X_pow_eq_monomial, monomial_mul, one_mul]; rfl/' $f
sed -i 's/Finset.mem_antidiagonal\] at hx/Finset.HasAntidiagonal.mem_antidiagonal] at hx/' $f
sed -i 's/right; exact ih_placeholder/exact Or.inr h/' $f
