import Mathlib
open CategoryTheory Abelian
instance {R : Type} [CommRing R]: CategoryTheory.HasExt.{0} (ModuleCat.{0} R) :=
  CategoryTheory.hasExt_of_enoughProjectives (ModuleCat R)

theorem L1 {A : Type} [CommRing A] (I : Ideal A) (φ : I →ₗ[A] A)
    (h : ∀ ψ : A →ₗ[A] A, ¬ (∀ y : I, ψ y = φ y)) :
    ¬ Subsingleton (Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) 1) := by
  intro hs
  let S : ShortComplex (ModuleCat.{0} A) :=
    ShortComplex.mk (ModuleCat.ofHom (I.subtype)) (ModuleCat.ofHom (Submodule.mkQ I))
      (by ext x; exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype I)
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective I)
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, (Ideal.Quotient.eq_zero_iff_mem.1 hx)⟩, rfl⟩
  have ex := Ext.contravariant_sequence_exact₁' hS (ModuleCat.of A A) 0 1 (by simp)
  rw [ShortComplex.ab_exact_iff_ker_le_range] at ex
  have key := @ex (Ext.mk₀ (ModuleCat.ofHom φ)) (by
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _)
  obtain ⟨y, hy⟩ := key
  obtain ⟨g0, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  have hy2 : Ext.mk₀ (S.f ≫ g0) = Ext.mk₀ (ModuleCat.ofHom φ) := by
    rw [← Ext.mk₀_comp_mk₀]; exact hy
  have hy3 := (Ext.mk₀_bijective _ _).1 hy2
  apply h g0.hom
  intro z
  have := congrArg (fun e => e.hom z) hy3
  simpa [S] using this
