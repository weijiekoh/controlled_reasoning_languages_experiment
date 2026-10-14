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
  sorry
