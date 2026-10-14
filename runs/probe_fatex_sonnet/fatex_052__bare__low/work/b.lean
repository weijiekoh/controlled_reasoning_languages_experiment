import Mathlib
open Polynomial
example (R : Type) [CommRing R] (m : Ideal R)
    (h_le_jac : m ≤ Ring.jacobson R) (G₁ G₂ : Polynomial R) (h_monic : G₁.Monic)
    (h_gen : Ideal.span {G₁.map (Ideal.Quotient.mk m), G₂.map (Ideal.Quotient.mk m)} = ⊤) :
    Ideal.span {G₁, G₂} = ⊤ := by
  set I : Ideal R[X] := Ideal.span {G₁, G₂} with hI
  have hle : Ideal.span {G₁} ≤ I := Ideal.span_mono (by simp)
  have := h_monic.finite_quotient
  have hfin : Module.Finite R (R[X] ⧸ I) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.factorₐ R hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  have htop : I ⊔ Ideal.map C m = ⊤ := by
    have e : Ideal.span {G₁.map (Ideal.Quotient.mk m), G₂.map (Ideal.Quotient.mk m)}
        = Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk m)) I := by
      rw [hI, Ideal.map_span]; simp [Set.image_pair]
    rw [e] at h_gen
    have hs2 := Ideal.comap_map_of_surjective (Polynomial.mapRingHom (Ideal.Quotient.mk m))
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective) I
    rw [h_gen, Ideal.comap_top] at hs2
    rw [hs2, ← RingHom.ker_eq_comap_bot, Polynomial.ker_mapRingHom, Ideal.mk_ker]
  sorry
