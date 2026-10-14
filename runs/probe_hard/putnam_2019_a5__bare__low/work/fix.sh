sed -i 's/:= Polynomial.X_sub_C_ne_zero 1 |>.trans_eq. (by simp) $/:= by simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)/' putnam_2019_a5.lean
sed -i 's/have := sub_pow_char (Polynomial (ZMod p)) (Polynomial.X : Polynomial (ZMod p)) 1/have : ((Polynomial.X : Polynomial (ZMod p)) - 1) ^ p = Polynomial.X ^ p - 1 ^ p := sub_pow_char _ _ _/' putnam_2019_a5.lean
sed -i '/simp only at this/d; /rw \[show p - 1 - (j+1) + 1 - 1/d; /have : ((p - 1 - j : ℕ) : Polynomial/d' putnam_2019_a5.lean
