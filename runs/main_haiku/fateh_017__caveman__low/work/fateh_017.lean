import Mathlib

open Polynomial

/--
Prove that $\frac{x^{p}-1}{x-1}$ is irreducible in $\mathbb{Z}[x].$
-/
theorem irreducible_X_pow_p_sub_one_div_X_sub_one (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Irreducible (((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1)) := by
  have hmon : (Polynomial.X - 1 : ℤ[X]).Monic := by
    rw [← C_1]; exact monic_X_sub_C 1
  have hq : ((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1) = cyclotomic p ℤ := by
    rw [cyclotomic_prime]
    have h : (Polynomial.X : ℤ[X]) ^ p - 1 = (Polynomial.X - 1) * ∑ i ∈ Finset.range p, (Polynomial.X : ℤ[X]) ^ i := by
      rw [mul_comm, geom_sum_mul]
    rw [h, mul_divByMonic_cancel_left _ hmon]
  rw [hq]
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom ℚ) _ (cyclotomic.monic p ℤ)
  rw [map_cyclotomic]
  exact cyclotomic.irreducible_rat hp.out.pos
