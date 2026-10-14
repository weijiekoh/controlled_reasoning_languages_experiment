import Mathlib

open Polynomial

/--
Prove that $\frac{x^{p}-1}{x-1}$ is irreducible in $\mathbb{Z}[x].$
-/
theorem irreducible_X_pow_p_sub_one_div_X_sub_one (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Irreducible (((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1)) := by
  have h1 : ((Polynomial.X : ℤ[X]) ^ p - 1) = cyclotomic p ℤ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
  have hm : (X - 1 : ℤ[X]).Monic := monic_X_sub_C 1
  rw [h1, mul_comm, mul_divByMonic_cancel_left _ hm]
  have hprim : (cyclotomic p ℤ).IsPrimitive := (cyclotomic.monic p ℤ).isPrimitive
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim]
  rw [map_cyclotomic_int]
  exact cyclotomic.irreducible_rat hp.out.pos
