import Mathlib
open Polynomial
#check @FiniteField.sum_pow_lt_card_sub_one
#check @FiniteField.sum_pow_card_sub_one_eq_neg_one
#check @Polynomial.taylor_coeff
#check @Polynomial.taylor_mul
#check @Polynomial.taylor_taylor
#check @Polynomial.X_pow_dvd_iff
#check @Polynomial.hasseDeriv_coeff
#check @Polynomial.eval_eq_sum_range
#check @Polynomial.eval_eq_sum_range'
#check @descPochhammer_eval_eq_descFactorial
example (p : ℕ) (k : ℕ) (a : ZMod p) (h : a = ((k : ℕ) ^ ((p - 1) / 2)) % p) : True := by
  set_option pp.all false in
  trivial
#check fun (p k : ℕ) => (((k : ℕ) ^ ((p - 1) / 2)) % p : ZMod p)
