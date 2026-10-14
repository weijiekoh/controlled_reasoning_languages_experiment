import Mathlib

open Polynomial

/--
Prove that $k[x,y]$ is not a Dedekind ring.
-/
theorem not_isDedekindRing_mvPolynomial_fin_two {k : Type} [Field k] :
    ¬ IsDedekindRing (MvPolynomial (Fin 2) k) := by
  intro h
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hbot : Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hX
  have hprime : (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)}).IsPrime :=
    (Ideal.span_singleton_prime hX).mpr MvPolynomial.X_prime
  have hmax := Ring.DimensionLEOne.maximalOfPrime hbot hprime
  let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}
  have hle : Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)} ≤ I := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.subset_span (by simp)
  have hIt : I ≠ ⊤ := by
    intro ht
    have h1 : (1 : MvPolynomial (Fin 2) k) ∈ I := by rw [ht]; trivial
    have hker : I ≤ RingHom.ker (MvPolynomial.aeval (R := k) (fun _ => (0 : k))) := by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp
    have := hker h1
    simp at this
  have hne : I ≠ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) k)} := by
    intro heq
    have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ I :=
      Ideal.subset_span (by simp)
    rw [heq, Ideal.mem_span_singleton] at hX1
    obtain ⟨q, hq⟩ := hX1
    have := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (0 : k) else 1)) hq
    simp at this
  exact hne (hmax.eq_of_le hIt hle).symm
