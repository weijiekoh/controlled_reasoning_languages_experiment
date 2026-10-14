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
  have hN := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m (⊤ : Submodule R (R[X] ⧸ I))
    Module.Finite.fg_top ?_ (by rw [Ideal.jacobson_bot]; exact h_le_jac)
  · have h1 : (1 : R[X] ⧸ I) = 0 := by
      have : (1 : R[X] ⧸ I) ∈ (⊥ : Submodule R (R[X] ⧸ I)) := hN ▸ Submodule.mem_top
      simpa using this
    have : (1 : R[X]) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; simpa using h1
    exact (Ideal.eq_top_iff_one _).2 this
  · intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : p ∈ I ⊔ Ideal.map C m := by rw [htop]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
    have : Ideal.Quotient.mk I (a + b) = Ideal.Quotient.mk I b := by
      rw [map_add, (Ideal.Quotient.eq_zero_iff_mem).2 ha, zero_add]
    rw [this, b.as_sum_range_C_mul_X_pow, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : b.coeff i ∈ m := (Ideal.mem_map_C_iff.1 hb) i
    have : Ideal.Quotient.mk I (C (b.coeff i) * X ^ i) = b.coeff i • Ideal.Quotient.mk I (X ^ i) := by
      rw [← Polynomial.smul_eq_C_mul]; rfl
    rw [this]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
