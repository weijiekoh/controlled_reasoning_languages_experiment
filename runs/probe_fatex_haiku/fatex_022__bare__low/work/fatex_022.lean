import Mathlib

namespace Problem22

/--
Let $F$ be a field with $\mathbb{Q} \subseteq F \subseteq \mathbb{C}$, where $F/\mathbb{Q}$
is a finite \emph{abelian} Galois extension. Prove that $F$ contains only finitely many algebraic
integers (i.e. elements in $F$ whose minimal polynomial over $\mathbb{Q}$ have coefficients in
$\mathbb{Z}$) having absolute value $1$, and each of the algebraic integers is a root of unity.
-/
theorem finite_algebraic_integers_of_finite_module
    (F : IntermediateField ℚ ℂ) (h_fin : Module.Finite ℚ F) [IsGalois ℚ F]
    (h : IsMulCommutative (F ≃ₐ[ℚ] F)) : {x : F | IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1}.Finite ∧
    (∀ x : F, IsIntegral ℤ x → ‖(x : ℂ)‖ = 1 → ∃ n,  x ^ n = 1) := by
  let : FiniteDimensional ℚ F := h_fin
  let : NumberField F := ⟨⟩
  have hmem : ∀ (x : F) (α : ℂ), Polynomial.aeval α (minpoly ℚ x) = 0 → α ∈ F := by
    intro x α hα
    have hs := Normal.splits (inferInstance : Normal ℚ F) x
    rw [Polynomial.splits_iff_exists_multiset] at hs
    obtain ⟨s, hs⟩ := hs
    have h2 := congrArg (Polynomial.map (algebraMap F ℂ)) hs
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h2
    have h3 := congrArg (Polynomial.eval α) h2
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hα] at h3
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map,
      Polynomial.map_sub, Polynomial.map_X, Function.comp_def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_sub, Polynomial.eval_X] at h3
    have hmon : (Polynomial.map (algebraMap ℚ F) (minpoly ℚ x)).Monic :=
      (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _
    have hlc : (algebraMap F ℂ) (Polynomial.map (algebraMap ℚ F) (minpoly ℚ x)).leadingCoeff ≠ 0 := by
      rw [hmon.leadingCoeff, map_one]; exact one_ne_zero
    have h4 := h3.symm
    rw [mul_eq_zero] at h4
    rcases h4 with h4 | h4
    · exact absurd h4 hlc
    · rw [Multiset.prod_eq_zero_iff] at h4
      obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h4
      have : α = algebraMap F ℂ a := by rw [sub_eq_zero] at ha; exact ha
      rw [this]; exact a.2
  have hconj : ∀ x : F, starRingEnd ℂ (x : ℂ) ∈ F := by
    intro x
    apply hmem x
    have hx : Polynomial.aeval (x : ℂ) (minpoly ℚ x) = 0 := by
      have := minpoly.aeval ℚ x
      have h := congrArg F.val this
      rw [← Polynomial.aeval_algHom_apply] at h
      simpa using h
    have key : starRingEnd ℂ (Polynomial.aeval (x : ℂ) (minpoly ℚ x)) =
        Polynomial.aeval (starRingEnd ℂ (x : ℂ)) (minpoly ℚ x) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext (fun q => by simp)
    rw [← key, hx, map_zero]
  let cA : F →ₐ[ℚ] F :=
    { toFun := fun x => ⟨starRingEnd ℂ (x : ℂ), hconj x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp)
      commutes' := fun q => Subtype.ext (by simp) }
  have hcc : ∀ x : F, cA (cA x) = x := fun x => Subtype.ext (by
    show starRingEnd ℂ (starRingEnd ℂ (x : ℂ)) = x
    simp)
  let c : F ≃ₐ[ℚ] F :=
    { cA with invFun := cA, left_inv := hcc, right_inv := hcc }
  have gen : ∀ g : F →+* ℂ, ∃ σ : F ≃ₐ[ℚ] F, ∀ y, (σ y : ℂ) = g y := by
    intro g
    let ψ : F →ₐ[ℚ] F :=
      { toFun := fun y => ⟨g y, by
          apply hmem y (g y)
          have := Polynomial.aeval_algHom_apply g.toRatAlgHom y (minpoly ℚ y)
          rw [minpoly.aeval, map_zero] at this
          exact this⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp)
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp)
        commutes' := fun q => Subtype.ext (by simp) }
    have hinj : Function.Injective ψ := by
      intro a b hab
      have hg : g a = g b := congrArg Subtype.val hab
      exact g.injective hg
    have hsurj : Function.Surjective ψ :=
      (LinearMap.injective_iff_surjective (f := ψ.toLinearMap)).mp hinj
    exact ⟨AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun y => rfl⟩
  have key : ∀ x : F, IsIntegral ℤ x → ‖(x : ℂ)‖ = 1 → ∀ φ : F →+* ℂ, ‖φ x‖ = 1 := by
    intro x _ hn φ
    obtain ⟨σ, hσ⟩ := gen φ
    have hcomm : σ * c = c * σ := h.is_comm.comm σ c
    have hcs : ∀ y : F, c (σ y) = σ (c y) := fun y => by
      have := congrArg (fun f : F ≃ₐ[ℚ] F => f y) hcomm
      simpa only [AlgEquiv.mul_apply] using this.symm
    have hxc1 : (x : ℂ) * starRingEnd ℂ (x : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    have hxc : x * c x = 1 := Subtype.ext (by
      show (x : ℂ) * starRingEnd ℂ (x : ℂ) = 1
      exact hxc1)
    have hprod : σ x * σ (c x) = 1 := by rw [← map_mul, hxc, map_one]
    have hprodC : (σ x : ℂ) * ((σ (c x) : F) : ℂ) = 1 := by
      have := congrArg (fun z : F => (z : ℂ)) hprod
      simpa using this
    have hE : starRingEnd ℂ (σ x : ℂ) = ((σ (c x) : F) : ℂ) := by
      rw [← hcs]; rfl
    have h1 : (σ x : ℂ) * starRingEnd ℂ (σ x : ℂ) = 1 := by rw [hE]; exact hprodC
    have h3 : Complex.normSq (σ x : ℂ) = 1 := by
      have := h1
      rw [Complex.mul_conj] at this
      exact_mod_cast this
    rw [Complex.normSq_eq_norm_sq] at h3
    rw [← hσ x]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h3
  constructor
  · apply Set.Finite.subset (NumberField.Embeddings.finite_of_norm_le F ℂ 1)
    intro x hx
    exact ⟨hx.1, fun φ => (key x hx.1 hx.2 φ).le⟩
  · intro x hi hn
    obtain ⟨n, _, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one F ℂ hi
      (fun φ => key x hi hn φ)
    exact ⟨n, hpow⟩

end Problem22
