perl -0pi -e 's/      show ρ \(X 0 \^ 3 \* X 1\) = 0\n      exact rho_b k/      have hb : ρ (X 0 ^ 3 * X 1) = 0 := rho_b k\n      exact hb/' main_part.lean
