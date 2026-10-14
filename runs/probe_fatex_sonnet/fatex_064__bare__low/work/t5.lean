import Mathlib
open MvPolynomial
example (k : Type) [Field k] : (Polynomial.evalRingHom 0).comp ((aeval (R := k) (S₁ := Polynomial k) ![Polynomial.X, 0] : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) : MvPolynomial (Fin 2) k →+* Polynomial k) = constantCoeff := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [MvPolynomial.aeval_C]
  · intro i; fin_cases i <;> simp [MvPolynomial.aeval_X]
