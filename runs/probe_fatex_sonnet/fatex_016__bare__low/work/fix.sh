f=fatex_016.lean
perl -0pi -e 's/        have := Nat\.eq_prime_pow_of_unique/    have := Nat.eq_prime_pow_of_unique/; s/    exact this\n  obtain/    exact ⟨_, this⟩\n  obtain/; s/exact \(minpoly\.algebraMap_eq[^\n]*/exact (IntermediateField.minpoly_eq L x).symm/' $f
