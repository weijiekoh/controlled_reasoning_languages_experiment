import Mathlib
open Polynomial
example {k : Type} [Field k] :
    ¬ IsDedekindRing (MvPolynomial (Fin 2) k) := by
  intro h
  let φ : MvPolynomial (Fin 2) k →ₐ[k] k[X] := MvPolynomial.aeval ![0, X]
  have hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hne : RingHom.ker φ ≠ ⊥ := by
    intro hb
    have : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈ RingHom.ker φ := by
      simp [φ, RingHom.mem_ker]
    rw [hb] at this
    simp at this
  have hm := h.toDimensionLEOne.maximalOfPrime hne hp
  have hs : Function.Surjective φ := by
    have : φ.comp (Polynomial.aeval (MvPolynomial.X 1)) = AlgHom.id k k[X] := by
      apply Polynomial.algHom_ext
      simp [φ]
    intro p
    refine ⟨Polynomial.aeval (MvPolynomial.X 1) p, ?_⟩
    exact congrArg (fun f => f p) this
  have hf := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hm
  have e := RingHom.quotientKerEquivOfSurjective (f := (φ : MvPolynomial (Fin 2) k →+* k[X])) hs
  have : IsField k[X] := e.symm.toMulEquiv.isField hf
  exact Polynomial.not_isField k this
