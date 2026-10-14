import Mathlib
open Polynomial IntermediateField

theorem f_irred : Irreducible (X ^ 4 - X ^ 2 - 1 : ℚ[X]) := sorry
theorem cplx : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ aeval (a : ℂ) (X ^ 4 - X ^ 2 - 1 : ℚ[X]) = 0 ∧
    aeval ((b : ℂ) * Complex.I) (X ^ 4 - X ^ 2 - 1 : ℚ[X]) = 0 := sorry

theorem field_main (p : ℚ[X]) (hp : p = X ^ 4 - X ^ 2 - 1) :
    ∃ χ : (p.SplittingField ≃ₐ[ℚ] p.SplittingField) →* Equiv.Perm (Fin 4), Function.Injective χ ∧
      (∀ g, χ g * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * χ g) ∧
      8 ≤ Nat.card (p.SplittingField ≃ₐ[ℚ] p.SplittingField) := by
  have hirr : Irreducible p := hp ▸ f_irred
  have hsep : p.Separable := hirr.separable
  have hdeg : p.natDegree = 4 := by rw [hp]; compute_degree!
  have hne : p ≠ 0 := hirr.ne_zero
  have hsp : (p.map (algebraMap ℚ p.SplittingField)).Splits := SplittingField.splits p
  haveI : IsSplittingField ℚ p.SplittingField p := Polynomial.IsSplittingField.splittingField p
  haveI : Fact (p.map (algebraMap ℚ p.SplittingField)).Splits := ⟨hsp⟩
  haveI : Normal ℚ p.SplittingField := Normal.of_isSplittingField p
  have hpa : ∀ (L : Type) [Field L] [Algebra ℚ L] (x : L), aeval x p = x ^ 4 - x ^ 2 - 1 := by
    intro L _ _ x; rw [hp]; simp
  obtain ⟨a, b, ha, hb, hza, hzc⟩ := cplx
  rw [← hp] at hza hzc
  let ι : p.SplittingField →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hmem : ∀ z : ℂ, aeval z p = 0 → ∃ r : p.SplittingField, r ∈ p.rootSet p.SplittingField ∧ ι r = z := by
    intro z hz
    have : z ∈ p.rootSet ℂ := (mem_rootSet).2 ⟨hne, hz⟩
    rw [← Splits.image_rootSet hsp ι] at this
    obtain ⟨r, hr, hrz⟩ := this
    exact ⟨r, hr, hrz⟩
  obtain ⟨ra, hra, hιa⟩ := hmem _ hza
  obtain ⟨rc, hrc, hιc⟩ := hmem _ hzc
  have hneg : ∀ r ∈ p.rootSet p.SplittingField, -r ∈ p.rootSet p.SplittingField := by
    intro r hr
    have h := (mem_rootSet.1 hr).2
    refine mem_rootSet.2 ⟨hne, ?_⟩
    rw [hpa] at h ⊢
    linear_combination h
  let e : Fin 4 → p.SplittingField := ![ra, -ra, rc, -rc]
  have he : ∀ i, e i ∈ p.rootSet p.SplittingField := by
    intro i; fin_cases i
    · exact hra
    · exact hneg _ hra
    · exact hrc
    · exact hneg _ hrc
  let w : Fin 4 → ℂ := ![(a : ℂ), -(a : ℂ), (b : ℂ) * Complex.I, -((b : ℂ) * Complex.I)]
  have hw : ∀ i, ι (e i) = w i := by
    intro i; fin_cases i <;> simp [e, w, hιa, hιc]
  have winj : Function.Injective w := by
    intro i j h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    fin_cases i <;> fin_cases j <;> simp [w] at hre him h ⊢ <;> linarith
  have einj : Function.Injective e := by
    intro i j h
    apply winj
    rw [← hw, ← hw, h]
  let e' : Fin 4 → ↥(p.rootSet p.SplittingField) := fun i => ⟨e i, he i⟩
  have e'inj : Function.Injective e' := fun i j h => einj (congrArg Subtype.val h)
  have e'bij : Function.Bijective e' := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨e'inj, ?_⟩
    rw [card_rootSet_eq_natDegree hsep hsp, hdeg]; simp
  let ε : Fin 4 ≃ ↥(p.rootSet p.SplittingField) := Equiv.ofBijective e' e'bij
  let χ : (p.SplittingField ≃ₐ[ℚ] p.SplittingField) →* Equiv.Perm (Fin 4) :=
    (Equiv.permCongrHom ε.symm).toMonoidHom.comp ((Gal.galActionHom p p.SplittingField).comp (Gal.restrict p p.SplittingField))
  have key : ∀ g i, e (χ g i) = g (e i) := by
    intro g i
    have h1 : ε (χ g i) = Gal.galActionHom p p.SplittingField (Gal.restrict p p.SplittingField g) (ε i) := by
      simp [χ, Equiv.permCongrHom, Equiv.permCongr_apply]
    have h2 := Gal.galActionHom_restrict p p.SplittingField g (ε i)
    rw [← h1] at h2
    exact h2
  have t0 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 0 = 1 := by decide
  have t1 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 1 = 0 := by decide
  have t2 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 2 = 3 := by decide
  have t3 : (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) 3 = 2 := by decide
  have hτ : ∀ i, e ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i) = - e i := by
    intro i; fin_cases i
    · simp only [Fin.zero_eta, t0]; rfl
    · simp only [Fin.mk_one, t1]; simp [e]
    · simp only [Fin.reduceFinMk, t2]; rfl
    · simp only [Fin.reduceFinMk, t3]; simp [e]
  have hsurj : ∀ r ∈ p.rootSet p.SplittingField, ∃ i, e i = r := by
    intro r hr
    obtain ⟨i, hi⟩ := e'bij.2 ⟨r, hr⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have χinj : Function.Injective χ := by
    intro g1 g2 h
    have : g1.toAlgHom = g2.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet p.SplittingField p)
      intro r hr
      obtain ⟨i, rfl⟩ := hsurj r hr
      have := key g1 i
      have h2 := key g2 i
      rw [h] at this
      show g1 (e i) = g2 (e i)
      rw [← this, h2]
    exact AlgEquiv.ext (fun x => by simpa using AlgHom.congr_fun this x)
  have χcomm : ∀ g, χ g * (Equiv.swap 0 1 * Equiv.swap 2 3) = (Equiv.swap 0 1 * Equiv.swap 2 3) * χ g := by
    intro g
    refine Equiv.ext fun i => ?_
    apply einj
    show e (χ g ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i)) = e ((Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) (χ g i))
    rw [key, hτ, hτ, map_neg, key]
  -- conjugation
  obtain ⟨σ, hσ⟩ : ∃ σ : p.SplittingField ≃ₐ[ℚ] p.SplittingField, ∀ x, ι (σ x) = (starRingEnd ℂ) (ι x) := by
    letI : Algebra p.SplittingField ℂ := ι.toRingHom.toAlgebra
    haveI : IsScalarTower ℚ p.SplittingField ℂ := IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
    refine ⟨(Complex.conjAe.restrictScalars ℚ).restrictNormal p.SplittingField, fun x => ?_⟩
    exact AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) p.SplittingField x
  have σa : σ ra = ra := by
    have : ι (σ ra) = ι ra := by rw [hσ, hιa, Complex.conj_ofReal]
    exact ι.injective this
  have σc : σ rc ≠ rc := by
    intro h
    have := hσ rc
    rw [h, hιc] at this
    have := congrArg Complex.im this
    simp at this
    linarith
  refine ⟨χ, χinj, χcomm, ?_⟩
  haveI := Gal.galAction_isPretransitive p p.SplittingField hirr
  let x0 : ↥(p.rootSet p.SplittingField) := ⟨ra, hra⟩
  have hidx := MulAction.index_stabilizer_of_transitive p.Gal x0
  have hR : Nat.card ↥(p.rootSet p.SplittingField) = 4 := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hsep hsp, hdeg]
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer p.Gal x0)
  have hst : 2 ≤ Nat.card (MulAction.stabilizer p.Gal x0) := by
    have : 1 < Nat.card (MulAction.stabilizer p.Gal x0) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      refine ⟨⟨⟨Gal.restrict p p.SplittingField σ, ?_⟩, 1, ?_⟩⟩
      · rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        have := Gal.galActionHom_restrict p p.SplittingField σ x0
        exact this.trans σa
      · intro h
        have h1 : Gal.restrict p p.SplittingField σ = 1 := congrArg Subtype.val h
        have := Gal.galActionHom_restrict p p.SplittingField σ ⟨rc, hrc⟩
        rw [h1, map_one] at this
        exact σc this.symm
    omega
  sorry
