import Mathlib

open Polynomial

/--
Prove that $\frac{x^{p}-1}{x-1}$ is irreducible in $\mathbb{Z}[x].$
-/
theorem irreducible_X_pow_p_sub_one_div_X_sub_one (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Irreducible (((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1)) := by
  have hm : (Polynomial.X - 1 : ℤ[X]).Monic := by
    simpa using monic_X_sub_C (1 : ℤ)
  have h : ((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1) = cyclotomic p ℤ := by
    rw [← cyclotomic_prime_mul_X_sub_one ℤ p, mul_comm, mul_divByMonic_cancel_left _ hm]
  rw [h, IsPrimitive.Int.irreducible_iff_irreducible_map_cast (cyclotomic.isPrimitive p ℤ),
    map_cyclotomic]
  exact cyclotomic.irreducible_rat hp.out.pos
