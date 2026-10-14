import Mathlib
open Polynomial

abbrev RS {I : Type} (p : I → ℕ) : Type :=
  Algebra.adjoin ℚ (Set.range (fun i ↦ Real.sqrt (p i)))

lemma fixedLemma {I : Type} [Finite I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (x : RS p) (hx : ∀ σ : RS p ≃ₐ[ℚ] RS p, σ x = x) : ∃ q : ℚ, (x : ℝ) = q := by
  have := Fintype.ofFinite I
  let S : Set ℝ := Set.range (fun i ↦ Real.sqrt (p i))
  let K' : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ S
  have hK : K'.toSubalgebra = Algebra.adjoin ℚ S := by
    apply IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    rintro _ ⟨i, rfl⟩
    apply IsIntegral.isAlgebraic
    refine ⟨X^2 - C (p i : ℚ), ?_, ?_⟩
    · exact monic_X_pow_sub_C _ (by norm_num)
    · simp [Real.sq_sqrt]
  let e : RS p ≃ₐ[ℚ] K' := (Subalgebra.equivOfEq _ _ hK.symm).trans (AlgEquiv.refl)
  let f : ℚ[X] := ∏ i, (X^2 - C (p i : ℚ))
  have hsp : Polynomial.IsSplittingField ℚ K' f := by
    refine IntermediateField.isSplittingField_iff.2 ?_
    constructor
    · sorry
    · sorry
  have := hsp
  have : FiniteDimensional ℚ K' := Polynomial.IsSplittingField.finiteDimensional K' f
  have hN : Normal ℚ K' := Normal.of_isSplittingField f
  have : IsGalois ℚ K' := ⟨⟩
  have : e x ∈ (⊥ : IntermediateField ℚ K') := by
    rw [IsGalois.mem_bot_iff_fixed]
    intro τ
    have := hx (e.trans (τ.trans e.symm))
    simpa using congrArg e this
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 this
  refine ⟨q, ?_⟩
  have := congrArg (fun y : K' => (y : ℝ)) hq
  have h2 : ((e x : K') : ℝ) = (x:ℝ) := rfl
  rw [← h2]; simpa using this.symm
